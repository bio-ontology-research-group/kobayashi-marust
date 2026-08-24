//! Worker entrypoints for the multi-call `km` binary and the standalone shims.
//!
//! The reasoner ships as ONE binary: `km classify` is the orchestrator and
//! `km ofn|elc|engine|tableau` are the workers it spawns (re-invoking itself via
//! `current_exe`). The historical standalone binaries (`ofn`, `elc`,
//! `kobayashi-marust`, `tableau_cli`) remain as thin shims that call straight
//! into these same functions, so nothing that hard-codes a worker path breaks.
//!
//! Each function reads its stdin/args, writes stdout, and `exit`s with the exact
//! code the standalone binary used (3 = out-of-fragment / not-EL, 4 = elc PARTIAL
//! certificate, 1 = error), so behaviour is byte-identical either way.

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::process::exit;

use crate::json_io::{JClause, JInput, JOutput};

/// Convenience debug switch: if `--debug` (or `--debug-probe`) is anywhere on the
/// command line, turn on the diagnostic tracing env vars before the worker runs,
/// so a user does not have to remember to `export` them.
///   `--debug`       → `KM_HT_TRACE` (routing decisions, per-phase wall timing, the
///                     QOSAT/QODRAIN/QOEDGE saturation heartbeats with elapsed s).
///   `--debug-probe` → additionally `KM_HT_QO_EDGEPROBE` (per-primitive work-volume
///                     counters + the time-driven `QOHB` heartbeat that stays live
///                     during a throughput collapse).
/// Explicitly-set env vars are never overridden. Recognised by every worker, so it
/// works for both `km tableau --debug` and the standalone `tableau_cli --debug`.
/// SIGUSR1 handler (debug only): dump the interrupted thread's stack. Lets a
/// throughput sink be located without an external sampler (none are installed on
/// the build host). `force_capture` allocates, so it is NOT async-signal-safe —
/// this is a one-shot diagnostic used only under `--debug-probe`, never in
/// production. Send it to the spinning worker thread with
/// `kill -USR1 <tid>` (the TID from `/proc/<pid>/task` whose `stat` shows the CPU).
#[cfg(unix)]
extern "C" fn km_sigusr1_bt(_sig: i32) {
    let bt = std::backtrace::Backtrace::force_capture();
    eprintln!("\n=== SIGUSR1 backtrace ===\n{bt}\n=== end backtrace ===");
}

pub fn maybe_enable_debug() {
    let mut trace = false;
    let mut probe = false;
    for a in std::env::args() {
        match a.as_str() {
            "--debug" => trace = true,
            "--debug-probe" => {
                trace = true;
                probe = true;
            }
            _ => {}
        }
    }
    if trace && std::env::var_os("KM_HT_TRACE").is_none() {
        std::env::set_var("KM_HT_TRACE", "1");
    }
    if probe && std::env::var_os("KM_HT_QO_EDGEPROBE").is_none() {
        // The value doubles as the QOEDGE per-pop print interval, so a small value
        // (e.g. 1) prints every pop and makes the run stderr-I/O-bound — use a
        // coarse interval; the time-driven `QOHB` heartbeat is the real probe and
        // is independent of this. Override by exporting KM_HT_QO_EDGEPROBE yourself.
        std::env::set_var("KM_HT_QO_EDGEPROBE", "200000");
    }
    if probe {
        // Install the SIGUSR1 stack-dumper so a stuck worker can be sampled.
        #[cfg(unix)]
        unsafe {
            libc::signal(libc::SIGUSR1, km_sigusr1_bt as usize as libc::sighandler_t);
        }
        if std::env::var_os("RUST_BACKTRACE").is_none() {
            std::env::set_var("RUST_BACKTRACE", "1");
        }
    }
}

// ---------------------------------------------------------------------------
// ofn — OWL functional-syntax normalisation frontend
// ---------------------------------------------------------------------------
#[derive(serde::Serialize)]
struct OfnOutput {
    clauses: Vec<JClause>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rbox: Vec<Vec<String>>,
    iri_map: BTreeMap<String, String>,
    named: Vec<String>,
    declared: Vec<String>,
    el_rbox_safe: bool,
    abox_inconsistent: bool,
    asserted_classes: Vec<String>,
    #[serde(skip_serializing_if = "crate::json_io::NominalAboxMeta::is_empty")]
    nominal_abox: crate::json_io::NominalAboxMeta,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    cardinalities: Vec<crate::json_io::CardMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    definers: Vec<crate::json_io::DefinerMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rules: Vec<crate::json_io::JRule>,
}

#[derive(serde::Serialize)]
struct OfnMeta {
    iri_map: BTreeMap<String, String>,
    named: Vec<String>,
    declared: Vec<String>,
    el_rbox_safe: bool,
    abox_inconsistent: bool,
    asserted_classes: Vec<String>,
    profile: crate::frontend::profile::OntologyProfile,
    route: String,
}

#[derive(serde::Serialize)]
struct OfnClausesOnly {
    clauses: Vec<JClause>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rbox: Vec<Vec<String>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    cardinalities: Vec<crate::json_io::CardMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    definers: Vec<crate::json_io::DefinerMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
    #[serde(skip_serializing_if = "crate::json_io::NominalAboxMeta::is_empty")]
    nominal_abox: crate::json_io::NominalAboxMeta,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rules: Vec<crate::json_io::JRule>,
}

/// `args` are the post-subcommand arguments: `args[0]` = ontology path, with
/// optional `--meta <meta.json>` and `--elc-binary <clauses.bin>` outputs. (For
/// the standalone `ofn` binary this is `env::args()[1..]`; for `km ofn` it is
/// `env::args()[2..]`.)
pub fn run_ofn(args: &[String]) {
    use crate::frontend::ofn_to_clauses;
    if args.is_empty() {
        eprintln!("usage: ofn <ontology.ofn> [--meta <meta.json>] [--elc-binary <clauses.bin>]");
        exit(2);
    }
    let path = &args[0];
    let mut meta_path: Option<&str> = None;
    let mut elc_binary_path: Option<&str> = None;
    let mut index = 1;
    while index < args.len() {
        let (slot, name) = match args[index].as_str() {
            "--meta" => (&mut meta_path, "--meta"),
            "--elc-binary" => (&mut elc_binary_path, "--elc-binary"),
            option => {
                eprintln!("unknown ofn option: {option}");
                exit(2);
            }
        };
        let Some(value) = args.get(index + 1) else {
            eprintln!("{name} requires a path argument");
            exit(2);
        };
        *slot = Some(value);
        index += 2;
    }
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
    let binary_route = result.route.parse::<crate::routing::Route>().ok();
    // Both EL-first routes can consume the compact typed-clause sidecar. A
    // CertifiedElProduction refusal recursively reruns the frontend under its
    // mandatory ProductionAll fallback, so pre-serialising a giant JSON clause
    // stream that the successful EL arm never reads is unnecessary.
    // Exact EL always benefits from the compact handoff. For a certified EL
    // route, measurements show that paying for both the binary encoding and
    // its isolated worker only amortises on very large source documents. Keep
    // the established JSON handoff below 512 MiB.
    let binary_el_route = matches!(binary_route, Some(crate::routing::Route::Elc))
        || (matches!(
            binary_route,
            Some(crate::routing::Route::CertifiedElProduction)
        ) && text.len() >= 512 * 1024 * 1024);
    let mut binary_written = false;
    if result.el_rbox_safe && binary_el_route {
        if let Some(binary_path) = elc_binary_path {
            let write_result = std::fs::File::create(binary_path).and_then(|file| {
                let mut writer = std::io::BufWriter::new(file);
                crate::json_io::write_elc_binary(&mut writer, &result.clauses)?;
                writer.flush()
            });
            if let Err(error) = write_result {
                eprintln!("ELC binary serialise error: {error}");
                exit(1);
            }
            binary_written = true;
        }
    }
    // The frontend result owns everything needed below. Release the potentially
    // very large source document before serialising the clause array so both do
    // not contribute to the same peak.
    drop(text);
    // Stream JSON to a buffered stdout (the clause array dominates peak memory).
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());
    let binary_only = binary_written
        && !result.profile.positive_el_abox_materializable
        && result.profile.source.rule_axioms == 0;

    if let Some(mp) = meta_path {
        let meta = OfnMeta {
            iri_map: result.iri_map,
            named: result.named,
            declared: result.declared,
            el_rbox_safe: result.el_rbox_safe,
            abox_inconsistent: result.abox_inconsistent,
            asserted_classes: result.asserted_classes,
            profile: result.profile,
            route: result.route,
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
        // Successful EL-first routes consume the compact sidecar. Emitting the
        // same multi-gigabyte clause set as JSON is dead serialization and disk
        // traffic; a certified-route refusal reruns this frontend under the
        // production fallback. Positive ABox and rule checks still consume the
        // full JSON side channels and therefore retain established output.
        if binary_only {
            let _ = w.flush();
            return;
        }
        let out = OfnClausesOnly {
            clauses: result.clauses,
            rbox: result.rbox,
            cardinalities: result.cardinalities,
            definers: result.definers,
            source_axioms: result.source_axioms,
            nominal_abox: result.nominal_abox,
            rules: result.rules,
        };
        if let Err(e) = serde_json::to_writer(&mut w, &out) {
            eprintln!("serialise error: {}", e);
            exit(1);
        }
    } else {
        let out = OfnOutput {
            clauses: result.clauses,
            rbox: result.rbox,
            iri_map: result.iri_map,
            named: result.named,
            declared: result.declared,
            el_rbox_safe: result.el_rbox_safe,
            abox_inconsistent: result.abox_inconsistent,
            asserted_classes: result.asserted_classes,
            nominal_abox: result.nominal_abox,
            cardinalities: result.cardinalities,
            definers: result.definers,
            source_axioms: result.source_axioms,
            rules: result.rules,
        };
        if let Err(e) = serde_json::to_writer(&mut w, &out) {
            eprintln!("serialise error: {}", e);
            exit(1);
        }
    }
    let _ = w.write_all(b"\n");
    let _ = w.flush();
}

// ---------------------------------------------------------------------------
// elc — EL++ completion fast path
// ---------------------------------------------------------------------------
#[derive(serde::Serialize)]
struct ElcOutput {
    subsumptions: BTreeMap<String, Vec<String>>,
    inconsistent: bool,
    dropped: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    unresolved: Vec<String>,
}

pub fn run_elc() {
    use crate::elcomplete;
    use std::time::Instant;
    let timing = std::env::var("KM_ELC_TIMING").is_ok();
    let t0 = Instant::now();
    // Raw bytes + `from_slice` skips full-buffer UTF-8 validation (matters on the
    // ~750 MB ORE giants that classify right at the timeout).
    let mut buf: Vec<u8> = Vec::new();
    if let Err(e) = std::io::stdin().lock().read_to_end(&mut buf) {
        eprintln!("failed to read stdin: {}", e);
        exit(1);
    }
    if timing {
        eprintln!(
            "KM_ELC_TIMING read={:.2}s ({} MB)",
            t0.elapsed().as_secs_f64(),
            buf.len() >> 20
        );
    }
    let t1 = Instant::now();
    let clauses = match crate::json_io::decode_elc_binary(&buf) {
        Ok(Some(clauses)) => clauses,
        Ok(None) => match serde_json::from_slice::<JInput>(&buf) {
            Ok(input) => input.clauses,
            Err(e) => {
                eprintln!("bad input JSON: {}", e);
                exit(1);
            }
        },
        Err(error) => {
            eprintln!("bad ELC binary input: {error}");
            exit(1);
        }
    };
    drop(buf);
    if timing {
        eprintln!(
            "KM_ELC_TIMING parse={:.2}s ({} clauses)",
            t1.elapsed().as_secs_f64(),
            clauses.len()
        );
    }
    let t2 = Instant::now();
    match elcomplete::classify(clauses) {
        Some(res) => {
            if timing {
                eprintln!(
                    "KM_ELC_TIMING classify={:.2}s ({} subjects)",
                    t2.elapsed().as_secs_f64(),
                    res.subsumptions.len()
                );
            }
            let t3 = Instant::now();
            let partial = !res.unresolved.is_empty();
            let out = ElcOutput {
                subsumptions: res.subsumptions,
                inconsistent: res.inconsistent,
                dropped: 0,
                unresolved: res.unresolved,
            };
            let stdout = std::io::stdout();
            let mut w = std::io::BufWriter::new(stdout.lock());
            // Keep the established JSON path for the ORE median band.  The
            // compact handoff is reserved for very dense taxonomies, where
            // repeated superclass strings dominate transfer and decoding.
            let compact = !partial
                // Two million relations require a large subject set in the
                // production taxonomies.  This guard keeps the relation-count
                // scan entirely off the sparse path.
                && out.subsumptions.len() >= 1_000
                && std::env::var_os("KM_ELC_OUTPUT_BINARY").is_some()
                && std::env::var_os("KM_NO_ELC_OUTPUT_BINARY").is_none()
                && {
                    let compact_min_relations =
                        std::env::var("KM_ELC_OUTPUT_BINARY_MIN_RELATIONS")
                            .ok()
                            .and_then(|value| value.parse::<usize>().ok())
                            .unwrap_or(2_000_000);
                    out.subsumptions.values().map(Vec::len).sum::<usize>()
                        >= compact_min_relations
                };
            let write_result = if compact {
                crate::json_io::write_elc_output_binary(
                    &mut w,
                    &out.subsumptions,
                    out.inconsistent,
                    out.dropped,
                )
            } else {
                serde_json::to_writer(&mut w, &out).map_err(std::io::Error::other)
            };
            if let Err(e) = write_result {
                eprintln!("serialise error: {}", e);
                exit(1);
            }
            let _ = w.flush();
            if timing {
                eprintln!(
                    "KM_ELC_TIMING serialise={:.2}s total={:.2}s compact={compact}",
                    t3.elapsed().as_secs_f64(),
                    t0.elapsed().as_secs_f64()
                );
            }
            if partial {
                exit(4); // certified for every subject EXCEPT the listed residue
            }
        }
        None => exit(3), // not EL++: caller uses the disjunctive context engine
    }
}

// ---------------------------------------------------------------------------
// incremental -- exact EL++/CB/direct-HT session (JSONL stdin/stdout)
// ---------------------------------------------------------------------------

pub fn run_incremental() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let reader = std::io::BufReader::new(stdin.lock());
    let writer = std::io::BufWriter::new(stdout.lock());
    if let Err(error) = crate::incremental::run_jsonl_session(reader, writer) {
        eprintln!("incremental session I/O error: {error}");
        exit(1);
    }
}

// ---------------------------------------------------------------------------
// engine — the consequence-based disjunctive context saturation reasoner
// ---------------------------------------------------------------------------
pub fn run_engine() {
    use crate::reasoner::Reasoner;
    maybe_enable_debug();
    // KM_PROF_TIME: coarse whole-run phase timers (read+parse / build /
    // saturate / extract / serialise+write), complementing the per-rule timers
    // in engine.rs which only cover the saturation loop's rule bodies.
    let prof = std::env::var_os("KM_PROF_TIME").is_some();
    let t0 = std::time::Instant::now();
    let mut buf = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
        eprintln!("failed to read stdin: {e}");
        exit(1);
    }
    if prof {
        eprintln!(
            "KM_STATS[phase] read={:.1}ms bytes={}",
            t0.elapsed().as_secs_f64() * 1e3,
            buf.len()
        );
    }
    let input: JInput = match serde_json::from_str(&buf) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("failed to parse input JSON: {e}");
            exit(1);
        }
    };
    // The raw JSON is dead once parsed; free it before saturation so it never
    // coexists with the peak context state (on the big CB-routed ontologies it
    // is hundreds of MB of dead weight held across the whole run).
    drop(buf);
    let t_parse = t0.elapsed();
    if prof {
        eprintln!(
            "KM_STATS[phase] parse-cumulative={:.1}ms clauses={}",
            t_parse.as_secs_f64() * 1e3,
            input.clauses.len()
        );
    }

    let t1 = std::time::Instant::now();
    let cb_typed_source = if let Some(source) = input.cb_typed_source.clone() {
        Some(source)
    } else if std::env::var_os("KM_CB_LEAN_REQUIRED").is_some()
        || std::env::var_os("KM_CB_DUMP_TYPED_SOURCE").is_some()
    {
        match crate::cb_source::typed_source_candidate(&input.clauses) {
            Ok(source) => Some(source),
            Err(error) => {
                eprintln!("CB typed-source compilation declined: {error}");
                exit(5);
            }
        }
    } else {
        None
    };
    if let (Some(path), Some(source)) = (
        std::env::var_os("KM_CB_DUMP_TYPED_SOURCE"),
        cb_typed_source.as_ref(),
    ) {
        let file = match std::fs::File::create(&path) {
            Ok(file) => file,
            Err(error) => {
                eprintln!("CB typed-source dump failed: {error}");
                exit(5);
            }
        };
        if let Err(error) = serde_json::to_writer_pretty(file, source) {
            eprintln!("CB typed-source dump failed: {error}");
            exit(5);
        }
    }
    let mut r = Reasoner::new(&input.clauses);
    // Likewise the parsed `JClause` block (String-owning IRIs, several times
    // the raw JSON size) is fully interned into the Reasoner; drop it before
    // saturation rather than at end of function.
    drop(input);
    let t_build = t1.elapsed();
    if prof {
        eprintln!("KM_STATS[phase] build={:.1}ms", t_build.as_secs_f64() * 1e3);
    }
    let t2 = std::time::Instant::now();
    r.saturate_releasing_input();
    let t_saturate = t2.elapsed();
    if r.incomplete() {
        eprintln!(
            "classification declined: a resource backstop was reached before the CB fixpoint"
        );
        exit(4);
    }
    if let Some(path) = std::env::var_os("KM_CB_LIVE_STATE") {
        if let Err(error) = r.write_live_terminal_snapshot(&path) {
            eprintln!("CB certification evidence emission failed: {error}");
            exit(5);
        }
    }
    let certified_subsumptions = if std::env::var_os("KM_CB_LEAN_REQUIRED").is_some() {
        match verify_cb_lean_publication(&r, cb_typed_source.as_ref()) {
            Ok(subsumptions) => Some(subsumptions),
            Err(error) => {
                eprintln!("CB Lean certification failed: {error}");
                exit(5);
            }
        }
    } else {
        None
    };

    let t3 = std::time::Instant::now();
    // The derived-clause echo doubles output volume and is only consumed by the
    // certificate path (KM_EMIT_CLAUSES); off it would blow the driver's RSS on
    // the giant ontologies. It reads the reasoner's subsumption map, so it is
    // built BEFORE the map is moved out below.
    let derived_clauses = if std::env::var_os("KM_EMIT_CLAUSES").is_some() {
        r.emit_clauses()
    } else {
        Vec::new()
    };
    let inconsistent = r.inconsistent();
    let dropped = r.dropped_unsupported();
    let production_subsumptions = r.take_subsumptions();
    let subsumptions = certified_subsumptions
        .unwrap_or(production_subsumptions)
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().collect::<Vec<_>>()))
        .collect();
    // The reasoner (contexts, clause arenas, indexes — the saturation peak) is
    // dead once the answer is moved out; free it before serialising so the
    // output bytes reuse that memory instead of stacking on top of it.
    drop(r);
    let t_extract = t3.elapsed();

    let out = JOutput {
        subsumptions,
        derived_clauses,
        inconsistent,
        dropped,
    };

    let t4 = std::time::Instant::now();
    // Stream the serialisation: `to_string` materialised the whole output as
    // one extra String (identical bytes either way).
    let stdout = std::io::stdout();
    let mut h = std::io::BufWriter::new(stdout.lock());
    serde_json::to_writer(&mut h, &out).expect("serialise output");
    h.write_all(b"\n").expect("write newline");
    h.flush().expect("flush stdout");
    if prof {
        eprintln!(
            "KM_STATS[phase-ms] parse={:.1} build={:.1} saturate={:.1} extract={:.1} write={:.1}",
            t_parse.as_secs_f64() * 1e3,
            t_build.as_secs_f64() * 1e3,
            t_saturate.as_secs_f64() * 1e3,
            t_extract.as_secs_f64() * 1e3,
            t4.elapsed().as_secs_f64() * 1e3,
        );
    }
}

fn cb_wire_term(term: crate::calc::Term, bits: u32) -> serde_json::Value {
    use crate::calc::{COMP_BASE, FTERM_BASE, X, Y};
    if term == X {
        return serde_json::json!({"var": {"index": 0}});
    }
    if term <= Y {
        return serde_json::json!({"var": {"index": i64::from(term) - i64::from(X)}});
    }
    if term < FTERM_BASE {
        return serde_json::json!({"constant": {"individual": term - X}});
    }
    if term < COMP_BASE {
        return serde_json::json!({"app": {
            "function": term - FTERM_BASE,
            "argument": {"var": {"index": 0}}
        }});
    }
    let packed = term - COMP_BASE;
    serde_json::json!({"app": {
        "function": packed >> bits,
        "argument": {"constant": {"individual": packed & ((1u32 << bits) - 1)}}
    }})
}

fn cb_wire_literal(literal: &crate::engine::CbLiveLit, bits: u32) -> serde_json::Value {
    match (literal.kind, literal.iri, literal.second) {
        ("concept", Some(concept), None) => serde_json::json!({"predicate": {
            "predicate": {"concept": {
                "concept": concept,
                "term": cb_wire_term(literal.first, bits)
            }}
        }}),
        ("role", Some(role), Some(target)) => serde_json::json!({"predicate": {
            "predicate": {"role": {
                "role": role,
                "source": cb_wire_term(literal.first, bits),
                "target": cb_wire_term(target, bits)
            }}
        }}),
        ("equality", None, Some(right)) => serde_json::json!({"equality": {
            "left": cb_wire_term(literal.first, bits),
            "right": cb_wire_term(right, bits)
        }}),
        ("inequality", None, Some(right)) => serde_json::json!({"inequality": {
            "left": cb_wire_term(literal.first, bits),
            "right": cb_wire_term(right, bits)
        }}),
        _ => serde_json::Value::Null,
    }
}

fn cb_wire_clause(clause: &crate::engine::CbLiveClause, bits: u32) -> serde_json::Value {
    serde_json::json!({
        "body": clause.body.iter().map(|literal| cb_wire_literal(literal, bits)).collect::<Vec<_>>(),
        "head": clause.head.iter().map(|literal| cb_wire_literal(literal, bits)).collect::<Vec<_>>(),
    })
}

fn cb_live_pred_literal(predicate: &crate::engine::CbLivePred) -> crate::engine::CbLiveLit {
    crate::engine::CbLiveLit {
        kind: predicate.kind,
        iri: Some(predicate.iri),
        first: predicate.first,
        second: predicate.second,
    }
}

fn cb_push_unique<T: PartialEq>(target: &mut Vec<T>, value: T) {
    if !target.contains(&value) {
        target.push(value);
    }
}

fn cb_resolve_live(
    positive: &crate::engine::CbLiveClause,
    negative: &crate::engine::CbLiveClause,
    literal: &crate::engine::CbLiveLit,
) -> Option<crate::engine::CbLiveClause> {
    if !positive.head.contains(literal) || !negative.body.contains(literal) {
        return None;
    }
    let mut body = Vec::new();
    for candidate in positive.body.iter().chain(negative.body.iter()) {
        if candidate != literal {
            cb_push_unique(&mut body, candidate.clone());
        }
    }
    let mut head = Vec::new();
    for candidate in positive.head.iter().chain(negative.head.iter()) {
        if candidate != literal {
            cb_push_unique(&mut head, candidate.clone());
        }
    }
    Some(crate::engine::CbLiveClause { body, head })
}

fn cb_clause_set_eq(
    left: &crate::engine::CbLiveClause,
    right: &crate::engine::CbLiveClause,
) -> bool {
    left.body.len() == right.body.len()
        && left.head.len() == right.head.len()
        && left.body.iter().all(|literal| right.body.contains(literal))
        && left.head.iter().all(|literal| right.head.contains(literal))
}

fn cb_hyper_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    prior: &std::collections::HashMap<(usize, bool, u32), usize>,
) -> Option<serde_json::Value> {
    let crate::engine::CbLiveRuleEvidence::Hyper {
        ontology_index,
        instantiated_source,
        context_clause_ids,
        matched_predicates,
        substitution,
    } = event.rule_evidence.as_ref()?
    else {
        return None;
    };
    if context_clause_ids.len() != matched_predicates.len() {
        return None;
    }
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let mut references = Vec::with_capacity(context_clause_ids.len());
    let mut providers = Vec::with_capacity(context_clause_ids.len());
    for &clause_id in context_clause_ids {
        let event_index = *prior.get(&(event.context_index, event.root, clause_id))?;
        references.push(serde_json::json!({"event_index": event_index}));
        providers.push(arena.get(clause_id as usize)?);
    }
    let mut trace = Vec::with_capacity(context_clause_ids.len() + 1);
    let wire_substitution = substitution
        .iter()
        .map(|entry| {
            serde_json::json!({
            "variableId": i64::from(entry.variable_id) - i64::from(crate::calc::X),
            "term": cb_wire_term(entry.value, live.comp_ind_bits),
            })
        })
        .collect::<Vec<_>>();
    trace.push(serde_json::json!({
        "clause": cb_wire_clause(instantiated_source, live.comp_ind_bits),
        "justification": {"premise": {
            "index": ontology_index,
            "substitution": wire_substitution,
        }}
    }));
    let premise_count = providers.len();
    let mut current = instantiated_source.clone();
    for (index, (provider, matched)) in providers.into_iter().zip(matched_predicates).enumerate() {
        let literal = cb_live_pred_literal(matched);
        current = cb_resolve_live(provider, &current, &literal)?;
        trace.push(serde_json::json!({
            "clause": cb_wire_clause(&current, live.comp_ind_bits),
            "justification": {"resolve": {
                "positive": index,
                "negative": premise_count + index,
                "literal": cb_wire_literal(&literal, live.comp_ind_bits),
            }}
        }));
    }
    let event_clause = arena.get(event.clause_id as usize)?;
    if !cb_clause_set_eq(&current, event_clause) {
        return None;
    }
    Some(serde_json::json!({
        "kind": "local",
        "prior_events": references,
        "trace": trace,
        "discarded": [],
    }))
}

fn cb_tautology_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
) -> Option<serde_json::Value> {
    if event.rule_hint != Some("succ") {
        return None;
    }
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let clause = arena.get(event.clause_id as usize)?;
    if !clause
        .body
        .iter()
        .any(|literal| clause.head.contains(literal))
    {
        return None;
    }
    Some(serde_json::json!({
        "kind": "local",
        "prior_events": [],
        "trace": [{
            "clause": cb_wire_clause(clause, live.comp_ind_bits),
            "justification": "tautology",
        }],
        "discarded": [],
    }))
}

fn cb_factor_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    prior: &std::collections::HashMap<(usize, bool, u32), usize>,
) -> Option<serde_json::Value> {
    let crate::engine::CbLiveRuleEvidence::Factor {
        source_clause_id,
        common,
        first,
        second,
    } = event.rule_evidence.as_ref()?
    else {
        return None;
    };
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let source = arena.get(*source_clause_id as usize)?;
    let removed = crate::engine::CbLiveLit {
        kind: "equality",
        iri: None,
        first: *common,
        second: Some(*first),
    };
    if !source.head.contains(&removed) || first == second {
        return None;
    }
    let mut expected = source.clone();
    expected.head.retain(|literal| literal != &removed);
    cb_push_unique(
        &mut expected.head,
        crate::engine::CbLiveLit {
            kind: "inequality",
            iri: None,
            first: *first,
            second: Some(*second),
        },
    );
    let result = arena.get(event.clause_id as usize)?;
    if !cb_clause_set_eq(&expected, result) {
        return None;
    }
    let source_event = *prior.get(&(event.context_index, event.root, *source_clause_id))?;
    Some(serde_json::json!({
        "kind": "local",
        "prior_events": [{"event_index": source_event}],
        "trace": [{
            "clause": cb_wire_clause(result, live.comp_ind_bits),
            "justification": {"factor": {
                "source": 0,
                "common": cb_wire_term(*common, live.comp_ind_bits),
                "first": cb_wire_term(*first, live.comp_ind_bits),
                "second": cb_wire_term(*second, live.comp_ind_bits),
            }}
        }],
        "discarded": [],
    }))
}

fn cb_rewrite_live_literal(
    literal: &crate::engine::CbLiveLit,
    left: crate::calc::Term,
    right: crate::calc::Term,
) -> Option<crate::engine::CbLiveLit> {
    let mut rewritten = literal.clone();
    match (literal.kind, literal.second) {
        ("concept", None) if literal.first == left => rewritten.first = right,
        ("role", Some(_)) if literal.first == left => rewritten.first = right,
        ("role", Some(target)) if target == left => rewritten.second = Some(right),
        ("equality" | "inequality", Some(_)) if literal.first == left => {
            rewritten.first = right;
        }
        _ => return None,
    }
    Some(rewritten)
}

fn cb_paramodulate_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    prior: &std::collections::HashMap<(usize, bool, u32), usize>,
) -> Option<serde_json::Value> {
    let crate::engine::CbLiveRuleEvidence::Paramodulate {
        equality_clause_id,
        other_clause_id,
        left,
        right,
        literal,
    } = event.rule_evidence.as_ref()?
    else {
        return None;
    };
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let equality_clause = arena.get(*equality_clause_id as usize)?;
    let other_clause = arena.get(*other_clause_id as usize)?;
    let equality = crate::engine::CbLiveLit {
        kind: "equality",
        iri: None,
        first: *left,
        second: Some(*right),
    };
    if !equality_clause.head.contains(&equality) || !other_clause.head.contains(literal) {
        return None;
    }
    let rewritten = cb_rewrite_live_literal(literal, *left, *right)?;
    let mut expected = crate::engine::CbLiveClause {
        body: Vec::new(),
        head: vec![rewritten.clone()],
    };
    for candidate in equality_clause.body.iter().chain(&other_clause.body) {
        cb_push_unique(&mut expected.body, candidate.clone());
    }
    for candidate in equality_clause
        .head
        .iter()
        .filter(|candidate| *candidate != &equality)
        .chain(
            other_clause
                .head
                .iter()
                .filter(|candidate| *candidate != literal),
        )
    {
        cb_push_unique(&mut expected.head, candidate.clone());
    }
    let result = arena.get(event.clause_id as usize)?;
    let mut trace = vec![serde_json::json!({
        "clause": cb_wire_clause(&expected, live.comp_ind_bits),
        "justification": {"paramodulate": {
            "equality": 0,
            "other": 1,
            "left": cb_wire_term(*left, live.comp_ind_bits),
            "right": cb_wire_term(*right, live.comp_ind_bits),
            "literal": cb_wire_literal(literal, live.comp_ind_bits),
        }}
    })];
    if cb_clause_set_eq(&expected, result) {
        trace[0]["clause"] = cb_wire_clause(result, live.comp_ind_bits);
    } else {
        if rewritten.kind != "inequality"
            || rewritten.first != *right
            || rewritten.second != Some(*right)
        {
            return None;
        }
        let mut filtered = expected.clone();
        filtered.head.retain(|candidate| candidate != &rewritten);
        if !cb_clause_set_eq(&filtered, result) {
            return None;
        }
        trace.push(serde_json::json!({
            "clause": cb_wire_clause(result, live.comp_ind_bits),
            "justification": {"deleteReflexiveInequality": {
                "source": 2,
                "term": cb_wire_term(*right, live.comp_ind_bits),
            }}
        }));
    }
    let equality_event = *prior.get(&(event.context_index, event.root, *equality_clause_id))?;
    let other_event = *prior.get(&(event.context_index, event.root, *other_clause_id))?;
    Some(serde_json::json!({
        "kind": "local",
        "prior_events": [
            {"event_index": equality_event},
            {"event_index": other_event},
        ],
        "trace": trace,
        "discarded": [],
    }))
}

fn cb_join_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    prior: &std::collections::HashMap<(usize, bool, u32), usize>,
) -> Option<serde_json::Value> {
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let result = arena.get(event.clause_id as usize)?;
    match event.rule_evidence.as_ref()? {
        crate::engine::CbLiveRuleEvidence::JoinResolve {
            consumer_clause_id,
            provider_clause_id,
            ground,
        } => {
            let consumer = arena.get(*consumer_clause_id as usize)?;
            let provider = arena.get(*provider_clause_id as usize)?;
            let live_literal = cb_live_pred_literal(ground);
            let expected = cb_resolve_live(provider, consumer, &live_literal)?;
            if !cb_clause_set_eq(&expected, result) {
                return None;
            }
            let provider_event =
                *prior.get(&(event.context_index, event.root, *provider_clause_id))?;
            let consumer_event =
                *prior.get(&(event.context_index, event.root, *consumer_clause_id))?;
            Some(serde_json::json!({
                "kind": "local",
                "prior_events": [
                    {"event_index": provider_event},
                    {"event_index": consumer_event},
                ],
                "trace": [{
                    "clause": cb_wire_clause(result, live.comp_ind_bits),
                    "justification": {"resolve": {
                        "positive": 0,
                        "negative": 1,
                        "literal": cb_wire_literal(&live_literal, live.comp_ind_bits),
                    }}
                }],
                "discarded": [],
            }))
        }
        crate::engine::CbLiveRuleEvidence::Join3 {
            consumer_clause_id,
            provider_clause_id,
            bridge_clause_id,
            ground,
            general,
            term,
        } => {
            let consumer = arena.get(*consumer_clause_id as usize)?;
            let provider = arena.get(*provider_clause_id as usize)?;
            let bridge = arena.get(*bridge_clause_id as usize)?;
            if !provider.body.is_empty() || !bridge.body.is_empty() {
                return None;
            }
            let ground_literal = cb_live_pred_literal(ground);
            let general_literal = cb_live_pred_literal(general);
            let mut instantiated_general = general.clone();
            if instantiated_general.first == crate::calc::X {
                instantiated_general.first = *term;
            }
            if instantiated_general.second == Some(crate::calc::X) {
                instantiated_general.second = Some(*term);
            }
            if &instantiated_general != ground {
                return None;
            }
            let bridge_literal = crate::engine::CbLiveLit {
                kind: "equality",
                iri: None,
                first: *term,
                second: Some(crate::calc::X),
            };
            if !consumer.body.contains(&ground_literal)
                || !provider.head.contains(&general_literal)
                || !bridge.head.contains(&bridge_literal)
            {
                return None;
            }
            let mut expected = crate::engine::CbLiveClause {
                body: consumer
                    .body
                    .iter()
                    .filter(|candidate| *candidate != &ground_literal)
                    .cloned()
                    .collect(),
                head: consumer.head.clone(),
            };
            for candidate in provider
                .head
                .iter()
                .filter(|candidate| *candidate != &general_literal)
                .chain(
                    bridge
                        .head
                        .iter()
                        .filter(|candidate| *candidate != &bridge_literal),
                )
            {
                cb_push_unique(&mut expected.head, candidate.clone());
            }
            if !cb_clause_set_eq(&expected, result) {
                return None;
            }
            let references = [*consumer_clause_id, *provider_clause_id, *bridge_clause_id]
            .into_iter()
            .map(|clause_id| {
                prior
                    .get(&(event.context_index, event.root, clause_id))
                    .copied()
                    .map(|event_index| serde_json::json!({"event_index": event_index}))
            })
            .collect::<Option<Vec<_>>>()?;
            Some(serde_json::json!({
                "kind": "local",
                "prior_events": references,
                "trace": [{
                    "clause": cb_wire_clause(result, live.comp_ind_bits),
                    "justification": {"join3": {
                        "consumer": 0,
                        "provider": 1,
                        "bridge": 2,
                        "ground": cb_wire_literal(&ground_literal, live.comp_ind_bits),
                        "general": cb_wire_literal(&general_literal, live.comp_ind_bits),
                        "term": cb_wire_term(*term, live.comp_ind_bits),
                    }}
                }],
                "discarded": [],
            }))
        }
        _ => None,
    }
}

fn cb_pred_backwards(
    term: crate::calc::Term,
    edge: crate::calc::Term,
    bits: u32,
) -> crate::calc::Term {
    use crate::calc::{COMP_BASE, X, Y};
    if edge >= COMP_BASE {
        let individual = X + ((edge - COMP_BASE) & ((1u32 << bits) - 1));
        return if term == Y {
            individual
        } else if term == X {
            edge
        } else {
            term
        };
    }
    if term == Y {
        X
    } else if term == X {
        edge
    } else {
        term
    }
}

fn cb_map_live_literal(
    literal: &crate::engine::CbLiveLit,
    map: impl Fn(crate::calc::Term) -> crate::calc::Term,
) -> crate::engine::CbLiveLit {
    crate::engine::CbLiveLit {
        kind: literal.kind,
        iri: literal.iri,
        first: map(literal.first),
        second: literal.second.map(map),
    }
}

fn cb_pred_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    prior: &std::collections::HashMap<(usize, bool, u32), usize>,
) -> Option<serde_json::Value> {
    let crate::engine::CbLiveRuleEvidence::Pred {
        sender_context_index,
        sender_clause_id,
        edge_label,
        payload,
        provider_clause_ids,
        matched_predicates,
    } = event.rule_evidence.as_ref()?
    else {
        return None;
    };
    let sender_context = live.contexts.get(*sender_context_index)?;
    let sender_arena = if sender_context.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let receiver_arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let sender_clause = sender_arena.get(*sender_clause_id as usize)?;
    let map = |term| cb_pred_backwards(term, *edge_label, live.comp_ind_bits);
    let mut expected_payload = crate::engine::CbLiveClause {
        body: sender_clause
            .body
            .iter()
            .map(|literal| cb_map_live_literal(literal, map))
            .collect(),
        head: sender_clause
            .head
            .iter()
            .map(|literal| cb_map_live_literal(literal, map))
            .collect(),
    };
    for predicate in &sender_context.core {
        cb_push_unique(
            &mut expected_payload.body,
            cb_map_live_literal(&cb_live_pred_literal(predicate), map),
        );
    }
    if !cb_clause_set_eq(&expected_payload, payload)
        || provider_clause_ids.len() != matched_predicates.len()
    {
        return None;
    }
    let mut current = payload.clone();
    let mut provider_events = Vec::with_capacity(provider_clause_ids.len());
    for (&clause_id, matched) in provider_clause_ids.iter().zip(matched_predicates) {
        let provider = receiver_arena.get(clause_id as usize)?;
        let literal = cb_live_pred_literal(matched);
        current = cb_resolve_live(provider, &current, &literal)?;
        provider_events.push(serde_json::json!({
            "event_index": *prior.get(&(event.context_index, event.root, clause_id))?
        }));
    }
    let result = receiver_arena.get(event.clause_id as usize)?;
    if !cb_clause_set_eq(&current, result) {
        return None;
    }
    let sender_event = *prior.get(&(
        *sender_context_index,
        sender_context.root,
        *sender_clause_id,
    ))?;
    Some(serde_json::json!({
        "kind": "pred",
        "prior_events": [],
        "trace": [],
        "discarded": [],
        "sender_event": {"event_index": sender_event},
        "provider_events": provider_events,
        "edge_label": cb_wire_term(*edge_label, live.comp_ind_bits),
        "payload": cb_wire_clause(payload, live.comp_ind_bits),
        "matched_predicates": matched_predicates
            .iter()
            .map(|predicate| cb_wire_literal(
                &cb_live_pred_literal(predicate), live.comp_ind_bits)["predicate"]
                ["predicate"]
                .clone())
            .collect::<Vec<_>>(),
    }))
}

fn cb_filtered_seed_trace(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
    initial: crate::engine::CbLiveClause,
    initial_justification: serde_json::Value,
) -> Option<serde_json::Value> {
    let arena = if event.root {
        &live.root_clause_arena
    } else {
        &live.ordinary_clause_arena
    };
    let target = arena.get(event.clause_id as usize)?;
    let mut current = initial;
    let mut trace = vec![serde_json::json!({
        "clause": cb_wire_clause(&current, live.comp_ind_bits),
        "justification": initial_justification,
    })];

    loop {
        let removable = current.head.iter().find_map(|literal| {
            live.source_ontology
                .iter()
                .enumerate()
                .find(|(_, source)| {
                    source.body.as_slice() == [literal.clone()] && source.head.is_empty()
                })
                .map(|(index, source)| (literal.clone(), index, source.clone()))
        });
        let Some((literal, ontology_index, bottom_clause)) = removable else {
            break;
        };
        let positive = trace.len() - 1;
        let negative = trace.len();
        trace.push(serde_json::json!({
            "clause": cb_wire_clause(&bottom_clause, live.comp_ind_bits),
            "justification": {"premise": {
                "index": ontology_index,
                "substitution": [],
            }},
        }));
        current = cb_resolve_live(&current, &bottom_clause, &literal)?;
        trace.push(serde_json::json!({
            "clause": cb_wire_clause(&current, live.comp_ind_bits),
            "justification": {"resolve": {
                "positive": positive,
                "negative": negative,
                "literal": cb_wire_literal(&literal, live.comp_ind_bits),
            }},
        }));
    }

    while let Some(literal) = current
        .head
        .iter()
        .find(|literal| literal.kind == "inequality" && literal.second == Some(literal.first))
        .cloned()
    {
        let source = trace.len() - 1;
        current.head.retain(|candidate| candidate != &literal);
        trace.push(serde_json::json!({
            "clause": cb_wire_clause(&current, live.comp_ind_bits),
            "justification": {"deleteReflexiveInequality": {
                "source": source,
                "term": cb_wire_term(literal.first, live.comp_ind_bits),
            }},
        }));
    }

    if !cb_clause_set_eq(&current, target) {
        return None;
    }
    Some(serde_json::json!({
        "kind": "local",
        "prior_events": [],
        "trace": trace,
        "discarded": [],
    }))
}

fn cb_filtered_seed_event_evidence(
    live: &crate::engine::CbLiveTerminalSnapshot,
    event: &crate::engine::CbLiveInsertionEvent,
) -> Option<serde_json::Value> {
    if event.rule_hint != Some("filtered-seed") || event.rule_evidence.is_some() {
        return None;
    }
    let context = live.contexts.get(event.context_index)?;
    for (index, predicate) in context.core.iter().enumerate() {
        let assumption = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(predicate)],
        };
        if let Some(evidence) = cb_filtered_seed_trace(
            live,
            event,
            assumption,
            serde_json::json!({"assumption": index}),
        ) {
            return Some(evidence);
        }
    }
    for (index, source) in live.source_ontology.iter().enumerate() {
        if source.body.is_empty() {
            if let Some(evidence) = cb_filtered_seed_trace(
                live,
                event,
                source.clone(),
                serde_json::json!({"premise": {
                    "index": index,
                    "substitution": [],
                }}),
            ) {
                return Some(evidence);
            }
        }
    }
    None
}

/// Construct the exact production-bound certificate bundle and require the
/// native Lean checker to accept it before any CB answer reaches stdout.
fn verify_cb_lean_publication(
    reasoner: &crate::reasoner::Reasoner,
    input_typed_source: Option<&serde_json::Value>,
) -> Result<std::collections::BTreeMap<String, std::collections::BTreeSet<String>>, String> {
    let source_live_checker =
        std::env::var_os("KM_CB_SOURCE_LIVE_DERIVATION_CHECKER");
    let source_live_path =
        std::env::var_os("KM_CB_SOURCE_LIVE_DERIVATION_CANDIDATE");
    if source_live_checker.is_some() && source_live_path.is_none() {
        return Err("KM_CB_SOURCE_LIVE_DERIVATION_CANDIDATE is required with \
            KM_CB_SOURCE_LIVE_DERIVATION_CHECKER"
            .to_string());
    }
    let source_local_checker =
        std::env::var_os("KM_CB_SOURCE_LOCAL_CLOSURE_CHECKER");
    let source_local_path =
        std::env::var_os("KM_CB_SOURCE_LOCAL_CLOSURE_CANDIDATE");
    if source_local_checker.is_some() && source_local_path.is_none() {
        return Err("KM_CB_SOURCE_LOCAL_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_LOCAL_CLOSURE_CHECKER"
            .to_string());
    }
    let source_hyper_checker = std::env::var_os("KM_CB_SOURCE_HYPER_CLOSURE_CHECKER");
    let source_hyper_path = std::env::var_os("KM_CB_SOURCE_HYPER_CLOSURE_CANDIDATE");
    if source_hyper_checker.is_some() && source_hyper_path.is_none() {
        return Err("KM_CB_SOURCE_HYPER_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_HYPER_CLOSURE_CHECKER".to_string());
    }
    let source_join3_checker = std::env::var_os("KM_CB_SOURCE_JOIN3_CLOSURE_CHECKER");
    let source_join3_path = std::env::var_os("KM_CB_SOURCE_JOIN3_CLOSURE_CANDIDATE");
    if source_join3_checker.is_some() && source_join3_path.is_none() {
        return Err("KM_CB_SOURCE_JOIN3_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_JOIN3_CLOSURE_CHECKER".to_string());
    }
    let source_succ_checker = std::env::var_os("KM_CB_SOURCE_SUCC_CLOSURE_CHECKER");
    let source_succ_path = std::env::var_os("KM_CB_SOURCE_SUCC_CLOSURE_CANDIDATE");
    if source_succ_checker.is_some() && source_succ_path.is_none() {
        return Err("KM_CB_SOURCE_SUCC_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_SUCC_CLOSURE_CHECKER".to_string());
    }
    let source_eq_checker = std::env::var_os("KM_CB_SOURCE_EQ_CLOSURE_CHECKER");
    let source_eq_path = std::env::var_os("KM_CB_SOURCE_EQ_CLOSURE_CANDIDATE");
    if source_eq_checker.is_some() && source_eq_path.is_none() {
        return Err("KM_CB_SOURCE_EQ_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_EQ_CLOSURE_CHECKER".to_string());
    }
    let source_ordinary_pred_checker =
        std::env::var_os("KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CHECKER");
    let source_ordinary_pred_path =
        std::env::var_os("KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CANDIDATE");
    if source_ordinary_pred_checker.is_some() && source_ordinary_pred_path.is_none() {
        return Err("KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CHECKER".to_string());
    }
    let source_root_pred_checker =
        std::env::var_os("KM_CB_SOURCE_ROOT_PRED_CLOSURE_CHECKER");
    let source_root_pred_path =
        std::env::var_os("KM_CB_SOURCE_ROOT_PRED_CLOSURE_CANDIDATE");
    if source_root_pred_checker.is_some() && source_root_pred_path.is_none() {
        return Err("KM_CB_SOURCE_ROOT_PRED_CLOSURE_CANDIDATE is required with \
            KM_CB_SOURCE_ROOT_PRED_CLOSURE_CHECKER".to_string());
    }
    let terminal_state_checker = std::env::var_os("KM_CB_TERMINAL_STATE_CHECKER");
    let terminal_state_path = std::env::var_os("KM_CB_TERMINAL_STATE_CANDIDATE");
    if terminal_state_checker.is_some() && terminal_state_path.is_none() {
        return Err("KM_CB_TERMINAL_STATE_CANDIDATE is required with \
            KM_CB_TERMINAL_STATE_CHECKER"
            .to_string());
    }
    let source_exact_checker = std::env::var_os("KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER");
    let source_exact_candidate_path =
        std::env::var_os("KM_CB_SOURCE_EXACT_TAXONOMY_CANDIDATE");
    if source_exact_checker.is_some() && source_exact_candidate_path.is_none() {
        return Err("KM_CB_SOURCE_EXACT_TAXONOMY_CANDIDATE is required with \
            KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER"
            .to_string());
    }
    let standalone_context_checker =
        std::env::var_os("KM_CB_STANDALONE_CONTEXT_PROOF_CHECKER");
    let standalone_context_path =
        std::env::var_os("KM_CB_STANDALONE_CONTEXT_PROOF_CANDIDATE");
    if standalone_context_checker.is_some() && standalone_context_path.is_none() {
        return Err("KM_CB_STANDALONE_CONTEXT_PROOF_CANDIDATE is required with \
            KM_CB_STANDALONE_CONTEXT_PROOF_CHECKER"
            .to_string());
    }
    let source_production_checker =
        std::env::var_os("KM_CB_SOURCE_PRODUCTION_TAXONOMY_CHECKER");
    let source_production_path =
        std::env::var_os("KM_CB_SOURCE_PRODUCTION_TAXONOMY_CANDIDATE");
    if source_production_checker.is_some() && source_production_path.is_none() {
        return Err("KM_CB_SOURCE_PRODUCTION_TAXONOMY_CANDIDATE is required with \
            KM_CB_SOURCE_PRODUCTION_TAXONOMY_CHECKER"
            .to_string());
    }
    let checker = std::env::var_os("KM_CB_LEAN_CERT_CHECKER");
    if checker.is_none()
        && source_exact_checker.is_none()
        && source_production_checker.is_none()
    {
        return Err(
            "KM_CB_LEAN_CERT_CHECKER, KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER, or \
             KM_CB_SOURCE_PRODUCTION_TAXONOMY_CHECKER is required"
                .to_string(),
        );
    }
    let bundle_path = std::env::var_os("KM_CB_CERT_BUNDLE")
        .ok_or_else(|| "KM_CB_CERT_BUNDLE is required".to_string())?;
    let derivation_candidate_path = std::env::var_os("KM_CB_DERIVATION_CANDIDATE");
    let exact_candidate_path = std::env::var_os("KM_CB_EXACT_TAXONOMY_CANDIDATE");
    let exact_checker = std::env::var_os("KM_CB_EXACT_LEAN_CERT_CHECKER");
    if exact_checker.is_some() && exact_candidate_path.is_none() {
        return Err(
            "KM_CB_EXACT_TAXONOMY_CANDIDATE is required with KM_CB_EXACT_LEAN_CERT_CHECKER"
                .to_string(),
        );
    }

    let global_model = if let Some(source) = input_typed_source {
        source.clone()
    } else if std::env::var_os("KM_CB_TEST_ALLOW_EXTERNAL_SOURCE").is_some() {
        let global_path = std::env::var_os("KM_CB_TYPED_SOURCE_CERT")
            .or_else(|| std::env::var_os("KM_CB_GLOBAL_MODEL_CERT"))
            .ok_or_else(|| {
                "certified CB input has no cb_typed_source and the test-only external source is not configured"
                    .to_string()
            })?;
        let global_bytes = std::fs::read(&global_path).map_err(|error| {
            format!(
                "cannot read test-only external CB certificate {}: {error}",
                std::path::Path::new(&global_path).display()
            )
        })?;
        serde_json::from_slice(&global_bytes)
            .map_err(|error| format!("cannot parse test-only external CB certificate: {error}"))?
    } else {
        return Err(
            "certified CB worker input requires an in-band cb_typed_source".to_string(),
        );
    };
    let live_state = reasoner.live_terminal_snapshot()?;
    let public_answer = reasoner.subsumptions();
    let public_inconsistent = reasoner.inconsistent();
    if reasoner.dropped_unsupported() != 0 {
        return Err(format!(
            "CB certified publication refuses {} unsupported input clauses",
            reasoner.dropped_unsupported()
        ));
    }
    let production_contexts = find_cb_production_contexts(&global_model, &live_state);
    let mut prior_insertions = std::collections::HashMap::new();
    let mut insertion_evidence = Vec::with_capacity(live_state.insertion_history.len());
    for event in &live_state.insertion_history {
        let automatic_derivation = if event.origin_hint == "derived" {
            cb_hyper_event_evidence(&live_state, event, &prior_insertions)
                .or_else(|| cb_factor_event_evidence(&live_state, event, &prior_insertions))
                .or_else(|| cb_paramodulate_event_evidence(&live_state, event, &prior_insertions))
                .or_else(|| cb_join_event_evidence(&live_state, event, &prior_insertions))
                .or_else(|| cb_pred_event_evidence(&live_state, event, &prior_insertions))
                .or_else(|| cb_tautology_event_evidence(&live_state, event))
                .or_else(|| cb_filtered_seed_event_evidence(&live_state, event))
        } else {
            None
        };
        let retained = live_state.contexts[event.context_index]
            .retained_clause_ids
            .contains(&event.clause_id);
        let trace = if event.origin_hint == "derived" && retained {
            production_contexts
                .and_then(|contexts| contexts.get(event.context_index))
                .and_then(|context| context.get("trace"))
                .and_then(serde_json::Value::as_array)
                .cloned()
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let discarded = if event.origin_hint == "derived" && !retained {
            production_contexts
                .and_then(|contexts| contexts.get(event.context_index))
                .and_then(|context| context.get("discarded"))
                .and_then(serde_json::Value::as_array)
                .cloned()
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let discarded_trace = if !discarded.is_empty() {
            production_contexts
                .and_then(|contexts| contexts.get(event.context_index))
                .and_then(|context| context.get("trace"))
                .and_then(serde_json::Value::as_array)
                .cloned()
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let fallback_kind = if event.origin_hint != "derived" {
            "seed"
        } else if retained && !trace.is_empty() {
            "local"
        } else if !discarded.is_empty() && !discarded_trace.is_empty() {
            "discarded"
        } else {
            "unproved"
        };
        let fallback = serde_json::json!({
            "kind": fallback_kind,
            "prior_events": [],
            "trace": if fallback_kind == "discarded" { discarded_trace } else { trace },
            "discarded": discarded,
        });
        insertion_evidence.push(automatic_derivation.unwrap_or(fallback));
        prior_insertions.insert(
            (event.context_index, event.root, event.clause_id),
            event.sequence,
        );
    }
    let production_bound = serde_json::json!({
        "version": 1,
        "global_model": global_model,
        "live_state": live_state,
    });
    let derivation = serde_json::json!({
        "version": 2,
        "production_bound": production_bound,
        "insertion_evidence": insertion_evidence,
    });
    let (public_rows, public_subsumptions, unsatisfiable) =
        cb_live_publication_rows(&live_state, &public_answer)?;
    let inconsistency_witness = if public_inconsistent {
        Some(cb_live_inconsistency_witness(&live_state)?)
    } else {
        None
    };
    let certificate = serde_json::json!({
        "version": 1,
        "derivation": derivation,
        "concept_names": live_state.concept_names,
        "public_rows": public_rows,
        "public_subsumptions": public_subsumptions,
        "unsatisfiable": unsatisfiable,
        "inconsistent": public_inconsistent,
        "inconsistency_witness": inconsistency_witness,
    });

    if let Some(path) = source_live_path.as_ref() {
        let candidate = cb_source_live_derivation_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound live CB certification requires an in-band typed source".to_string()
            })?,
            &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?,
        )?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!(
                "cannot create source-bound CB live candidate {}: {error}",
                std::path::Path::new(path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB live candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB live candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB live candidate: {error}"))?;
    }

    if let Some(path) = source_local_path.as_ref() {
        let live = cb_source_live_derivation_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound local CB certification requires an in-band typed source".to_string()
            })?,
            &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?,
        )?;
        let candidate = serde_json::json!({"version": 1, "live": live});
        let file = std::fs::File::create(path).map_err(|error| {
            format!(
                "cannot create source-bound CB local-closure candidate {}: {error}",
                std::path::Path::new(path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate).map_err(|error| {
            format!("cannot serialize source-bound CB local-closure candidate: {error}")
        })?;
        use std::io::Write;
        writer.write_all(b"\n").map_err(|error| {
            format!("cannot finish source-bound CB local-closure candidate: {error}")
        })?;
        writer.flush().map_err(|error| {
            format!("cannot flush source-bound CB local-closure candidate: {error}")
        })?;
    }

    if let Some(path) = source_hyper_path.as_ref() {
        let candidate = cb_source_hyper_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound Hyper certification requires an in-band typed source".to_string()
            })?,
            &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?,
        )?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB Hyper candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB Hyper candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB Hyper candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB Hyper candidate: {error}"))?;
    }

    if let Some(path) = source_join3_path.as_ref() {
        let hyper = cb_source_hyper_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound Join-3 certification requires an in-band typed source".to_string()
            })?, &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?)?;
        let candidate = serde_json::json!({"version": 1, "hyper_closure": hyper});
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB Join-3 candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB Join-3 candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB Join-3 candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB Join-3 candidate: {error}"))?;
    }

    if let Some(path) = source_succ_path.as_ref() {
        let candidate = cb_source_succ_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound Succ certification requires an in-band typed source".to_string()
            })?, &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?)?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB Succ candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB Succ candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB Succ candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB Succ candidate: {error}"))?;
    }

    if let Some(path) = source_eq_path.as_ref() {
        let candidate = cb_source_eq_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound Eq certification requires an in-band typed source".to_string()
            })?, &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?)?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB Eq candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB Eq candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB Eq candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB Eq candidate: {error}"))?;
    }

    if let Some(path) = source_ordinary_pred_path.as_ref() {
        let eq = cb_source_eq_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound ordinary Pred certification requires an in-band typed source"
                    .to_string()
            })?, &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?)?;
        let candidate = serde_json::json!({"version": 1, "eq_closure": eq});
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB ordinary Pred candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate).map_err(|error| {
            format!("cannot serialize source-bound CB ordinary Pred candidate: {error}")
        })?;
        use std::io::Write;
        writer.write_all(b"\n").map_err(|error| {
            format!("cannot finish source-bound CB ordinary Pred candidate: {error}")
        })?;
        writer.flush().map_err(|error| {
            format!("cannot flush source-bound CB ordinary Pred candidate: {error}")
        })?;
    }

    if let Some(path) = source_root_pred_path.as_ref() {
        let candidate = cb_source_root_pred_closure_candidate(
            input_typed_source.ok_or_else(|| {
                "source-bound root Pred certification requires an in-band typed source"
                    .to_string()
            })?, &live_state,
            certificate.pointer("/derivation/insertion_evidence")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB certificate omits insertion evidence".to_string())?)?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!("cannot create source-bound CB root Pred candidate {}: {error}",
                std::path::Path::new(path).display())
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-bound CB root Pred candidate: {error}"))?;
        use std::io::Write;
        writer.write_all(b"\n")
            .map_err(|error| format!("cannot finish source-bound CB root Pred candidate: {error}"))?;
        writer.flush()
            .map_err(|error| format!("cannot flush source-bound CB root Pred candidate: {error}"))?;
    }

    if let Some(path) = terminal_state_path.as_ref() {
        let terminal = cb_terminal_state_candidate(&global_model, &live_state)?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!(
                "cannot create CB terminal-state candidate {}: {error}",
                std::path::Path::new(path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &terminal)
            .map_err(|error| format!("cannot serialize CB terminal-state candidate: {error}"))?;
        use std::io::Write;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish CB terminal-state candidate: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush CB terminal-state candidate: {error}"))?;
    }
    let file = std::fs::File::create(&bundle_path).map_err(|error| {
        format!(
            "cannot create CB certificate bundle {}: {error}",
            std::path::Path::new(&bundle_path).display()
        )
    })?;
    let mut writer = std::io::BufWriter::new(file);
    serde_json::to_writer(&mut writer, &certificate)
        .map_err(|error| format!("cannot serialize CB certificate bundle: {error}"))?;
    use std::io::Write;
    writer
        .write_all(b"\n")
        .map_err(|error| format!("cannot finish CB certificate bundle: {error}"))?;
    writer
        .flush()
        .map_err(|error| format!("cannot flush CB certificate bundle: {error}"))?;

    if let Some(path) = standalone_context_path.as_ref() {
        let events = cb_public_witness_events(&certificate)?;
        let (document, _) = cb_standalone_context_proof_document(&certificate, &events)?;
        let file = std::fs::File::create(path).map_err(|error| {
            format!(
                "cannot create standalone CB context proof {}: {error}",
                std::path::Path::new(path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &document)
            .map_err(|error| format!("cannot serialize standalone CB context proof: {error}"))?;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish standalone CB context proof: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush standalone CB context proof: {error}"))?;
    }

    if let Some(path) = source_production_path.as_ref() {
        let (document, unresolved) = cb_source_production_taxonomy_candidate(&certificate)?;
        if unresolved != 0 {
            return Err(format!(
                "source-production CB taxonomy has {unresolved} unresolved cells"
            ));
        }
        let file = std::fs::File::create(path).map_err(|error| {
            format!(
                "cannot create source-production CB taxonomy {}: {error}",
                std::path::Path::new(path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &document).map_err(|error| {
            format!("cannot serialize source-production CB taxonomy: {error}")
        })?;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish source-production CB taxonomy: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush source-production CB taxonomy: {error}"))?;
    }

    if let Some(candidate_path) = derivation_candidate_path {
        let file = std::fs::File::create(&candidate_path).map_err(|error| {
            format!(
                "cannot create CB derivation candidate {}: {error}",
                std::path::Path::new(&candidate_path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &certificate)
            .map_err(|error| format!("cannot serialize CB derivation candidate: {error}"))?;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish CB derivation candidate: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush CB derivation candidate: {error}"))?;
    }

    let mut exact_unresolved = None;
    if let Some(candidate_path) = exact_candidate_path.as_ref() {
        let (candidate, unresolved) = cb_exact_taxonomy_candidate(&certificate)?;
        let file = std::fs::File::create(&candidate_path).map_err(|error| {
            format!(
                "cannot create exact CB taxonomy candidate {}: {error}",
                std::path::Path::new(&candidate_path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize exact CB taxonomy candidate: {error}"))?;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish exact CB taxonomy candidate: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush exact CB taxonomy candidate: {error}"))?;
        eprintln!("KM_CB_CERT exact taxonomy unresolved_negative_cells={unresolved}");
        exact_unresolved = Some(unresolved);
    }

    if let Some(source_checker) = source_live_checker {
        let path = source_live_path.as_ref().ok_or_else(|| {
            "source-bound CB live checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&source_checker)
            .arg(path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run source-bound CB live checker {}: {error}",
                    std::path::Path::new(&source_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "source-bound CB live checker rejected the candidate with {status}"
            ));
        }
    }
    if let Some(local_checker) = source_local_checker {
        let path = source_local_path.as_ref().ok_or_else(|| {
            "source-bound CB local-closure checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&local_checker)
            .arg(path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run source-bound CB local-closure checker {}: {error}",
                    std::path::Path::new(&local_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "source-bound CB local-closure checker rejected the candidate with {status}"
            ));
        }
    }
    if let Some(hyper_checker) = source_hyper_checker {
        let path = source_hyper_path.as_ref().ok_or_else(|| {
            "source-bound CB Hyper checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&hyper_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!("cannot run source-bound CB Hyper checker {}: {error}",
                std::path::Path::new(&hyper_checker).display()))?;
        if !status.success() {
            return Err(format!("source-bound CB Hyper checker rejected the candidate with {status}"));
        }
    }
    if let Some(join3_checker) = source_join3_checker {
        let path = source_join3_path.as_ref().ok_or_else(|| {
            "source-bound CB Join-3 checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&join3_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!("cannot run source-bound CB Join-3 checker {}: {error}",
                std::path::Path::new(&join3_checker).display()))?;
        if !status.success() {
            return Err(format!("source-bound CB Join-3 checker rejected the candidate with {status}"));
        }
    }
    if let Some(succ_checker) = source_succ_checker {
        let path = source_succ_path.as_ref().ok_or_else(|| {
            "source-bound CB Succ checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&succ_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!("cannot run source-bound CB Succ checker {}: {error}",
                std::path::Path::new(&succ_checker).display()))?;
        if !status.success() {
            return Err(format!("source-bound CB Succ checker rejected the candidate with {status}"));
        }
    }
    if let Some(eq_checker) = source_eq_checker {
        let path = source_eq_path.as_ref().ok_or_else(|| {
            "source-bound CB Eq checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&eq_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!("cannot run source-bound CB Eq checker {}: {error}",
                std::path::Path::new(&eq_checker).display()))?;
        if !status.success() {
            return Err(format!("source-bound CB Eq checker rejected the candidate with {status}"));
        }
    }
    if let Some(pred_checker) = source_ordinary_pred_checker {
        let path = source_ordinary_pred_path.as_ref().ok_or_else(|| {
            "source-bound CB ordinary Pred checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&pred_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!(
                "cannot run source-bound CB ordinary Pred checker {}: {error}",
                std::path::Path::new(&pred_checker).display()))?;
        if !status.success() {
            return Err(format!(
                "source-bound CB ordinary Pred checker rejected the candidate with {status}"));
        }
    }
    if let Some(pred_checker) = source_root_pred_checker {
        let path = source_root_pred_path.as_ref().ok_or_else(|| {
            "source-bound CB root Pred checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&pred_checker)
            .arg(path).stdout(std::process::Stdio::null()).status()
            .map_err(|error| format!("cannot run source-bound CB root Pred checker {}: {error}",
                std::path::Path::new(&pred_checker).display()))?;
        if !status.success() {
            return Err(format!(
                "source-bound CB root Pred checker rejected the candidate with {status}"));
        }
    }
    if let Some(checker) = checker {
        let status = std::process::Command::new(&checker)
            .arg(&bundle_path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run CB Lean checker {}: {error}",
                    std::path::Path::new(&checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!("CB Lean checker rejected the bundle with {status}"));
        }
    }
    if let Some(terminal_checker) = terminal_state_checker {
        let path = terminal_state_path
            .as_ref()
            .ok_or_else(|| "CB terminal-state checker has no candidate path".to_string())?;
        let status = std::process::Command::new(&terminal_checker)
            .arg(path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run CB terminal-state checker {}: {error}",
                    std::path::Path::new(&terminal_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "CB terminal-state checker rejected the candidate with {status}"
            ));
        }
    }
    if let Some(context_checker) = standalone_context_checker {
        let path = standalone_context_path
            .as_ref()
            .ok_or_else(|| "standalone CB context checker has no candidate path".to_string())?;
        let status = std::process::Command::new(&context_checker)
            .arg(path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run standalone CB context checker {}: {error}",
                    std::path::Path::new(&context_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "standalone CB context checker rejected the proof with {status}"
            ));
        }
    }
    if let Some(production_checker) = source_production_checker {
        let path = source_production_path.as_ref().ok_or_else(|| {
            "source-production CB taxonomy checker has no candidate path".to_string()
        })?;
        let status = std::process::Command::new(&production_checker)
            .arg(path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run source-production CB taxonomy checker {}: {error}",
                    std::path::Path::new(&production_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "source-production CB taxonomy checker rejected the matrix with {status}"
            ));
        }
    }
    if let Some(exact_checker) = exact_checker {
        let unresolved = exact_unresolved
            .ok_or_else(|| "exact CB checker has no generated matrix".to_string())?;
        if unresolved != 0 {
            return Err(format!(
                "exact CB taxonomy has {unresolved} unresolved negative cells"
            ));
        }
        let exact_path = exact_candidate_path
            .as_ref()
            .ok_or_else(|| "exact CB checker has no candidate path".to_string())?;
        let status = std::process::Command::new(&exact_checker)
            .arg(exact_path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run exact CB Lean checker {}: {error}",
                    std::path::Path::new(&exact_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "exact CB Lean checker rejected the matrix with {status}"
            ));
        }
    }
    if let Some(source_checker) = source_exact_checker {
        let source_path = source_exact_candidate_path
            .as_ref()
            .ok_or_else(|| "source-exact CB checker has no candidate path".to_string())?;
        let (candidate, unresolved) = cb_source_exact_taxonomy_candidate(&certificate)?;
        if unresolved != 0 {
            return Err(format!(
                "source-exact CB taxonomy has {unresolved} unresolved cells"
            ));
        }
        let file = std::fs::File::create(source_path).map_err(|error| {
            format!(
                "cannot create source-exact CB taxonomy candidate {}: {error}",
                std::path::Path::new(source_path).display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &candidate)
            .map_err(|error| format!("cannot serialize source-exact CB taxonomy: {error}"))?;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish source-exact CB taxonomy: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush source-exact CB taxonomy: {error}"))?;
        let status = std::process::Command::new(&source_checker)
            .arg(source_path)
            .stdout(std::process::Stdio::null())
            .status()
            .map_err(|error| {
                format!(
                    "cannot run source-exact CB Lean checker {}: {error}",
                    std::path::Path::new(&source_checker).display()
                )
            })?;
        if !status.success() {
            return Err(format!(
                "source-exact CB Lean checker rejected the matrix with {status}"
            ));
        }
    }
    Ok(public_answer)
}

fn cb_live_inconsistency_witness(
    live: &crate::engine::CbLiveTerminalSnapshot,
) -> Result<serde_json::Value, String> {
    for (context_index, context) in live.contexts.iter().enumerate() {
        if !context.core.is_empty() {
            continue;
        }
        let arena = if context.root {
            &live.root_clause_arena
        } else {
            &live.ordinary_clause_arena
        };
        if context.retained_clause_ids.iter().any(|&id| {
            arena
                .get(id as usize)
                .is_some_and(|clause| clause.body.is_empty() && clause.head.is_empty())
        }) {
            return Ok(serde_json::json!({"context_index": context_index}));
        }
    }
    Err("published CB inconsistency has no empty-core retained contradiction".to_string())
}

fn cb_dpll(clauses: &[Vec<i32>], atom_count: usize) -> Option<Vec<i8>> {
    fn search(clauses: &[Vec<i32>], assignment: &mut [i8], nodes: &mut usize) -> bool {
        *nodes += 1;
        if *nodes > 10_000 {
            return false;
        }
        loop {
            let mut changed = false;
            for clause in clauses {
                let mut satisfied = false;
                let mut open = 0usize;
                let mut unit = 0i32;
                for &literal in clause {
                    let atom = literal.unsigned_abs() as usize - 1;
                    let value = assignment[atom];
                    if value == 0 {
                        open += 1;
                        unit = literal;
                    } else if (literal > 0 && value > 0) || (literal < 0 && value < 0) {
                        satisfied = true;
                        break;
                    }
                }
                if satisfied {
                    continue;
                }
                if open == 0 {
                    return false;
                }
                if open == 1 {
                    let atom = unit.unsigned_abs() as usize - 1;
                    let value = if unit > 0 { 1 } else { -1 };
                    if assignment[atom] == -value {
                        return false;
                    }
                    if assignment[atom] == 0 {
                        assignment[atom] = value;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let Some(atom) = assignment.iter().position(|&value| value == 0) else {
            return true;
        };
        let checkpoint = assignment.to_vec();
        assignment[atom] = -1;
        if search(clauses, assignment, nodes) {
            return true;
        }
        assignment.copy_from_slice(&checkpoint);
        assignment[atom] = 1;
        if search(clauses, assignment, nodes) {
            return true;
        }
        assignment.copy_from_slice(&checkpoint);
        false
    }

    // Keep the diagnostic producer stack-safe on signatures that need a more
    // capable SAT/model backend. Such cells remain explicitly unresolved.
    if atom_count > 1024 {
        return None;
    }
    let mut assignment = vec![0i8; atom_count];
    let mut nodes = 0usize;
    search(clauses, &mut assignment, &mut nodes).then_some(assignment)
}

fn cb_finite_countermodel(
    live_state: &serde_json::Value,
    sub: usize,
    sup: usize,
    domain_size: usize,
) -> Result<Option<serde_json::Value>, String> {
    if domain_size == 0 {
        return Err("CB finite countermodel domain must be nonempty".to_string());
    }
    let count = |field: &str| -> Result<usize, String> {
        live_state
            .get(field)
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| format!("CB live state has no numeric {field}"))
    };
    let concept_count = count("concept_count")?;
    let role_count = count("role_count")?;
    let function_count = count("function_count")?;
    let individual_count = count("source_individual_count")?;
    if sub >= concept_count || sup >= concept_count {
        return Err("CB exact query coordinate exceeds the live concept bound".to_string());
    }
    let concept_atoms = concept_count
        .checked_mul(domain_size)
        .ok_or_else(|| "CB finite concept atom count overflow".to_string())?;
    let role_width = domain_size
        .checked_mul(domain_size)
        .ok_or_else(|| "CB finite role width overflow".to_string())?;
    let atom_count = role_count
        .checked_mul(role_width)
        .and_then(|roles| concept_atoms.checked_add(roles))
        .ok_or_else(|| "CB finite atom count overflow".to_string())?;
    let ontology = live_state
        .get("source_ontology")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "CB live state has no source_ontology array".to_string())?;
    let bits = live_state
        .get("comp_ind_bits")
        .and_then(serde_json::Value::as_u64)
        .and_then(|value| u32::try_from(value).ok())
        .unwrap_or(crate::calc::COMP_IND_BITS);
    if !(1..32).contains(&bits) {
        return Err("CB live packed-individual width is outside 1..31".to_string());
    }

    let decode_term = |raw: u32| -> Result<(Option<usize>, Option<usize>), String> {
        if raw <= crate::calc::X {
            return Ok((None, None));
        }
        if raw < crate::calc::FTERM_BASE {
            let individual = usize::try_from(raw - crate::calc::X)
                .map_err(|_| "CB individual id exceeds usize".to_string())?;
            if individual >= individual_count {
                return Err("CB live individual term exceeds its bound".to_string());
            }
            return Ok((Some(individual), None));
        }
        let function = if raw < crate::calc::COMP_BASE {
            usize::try_from(raw - crate::calc::FTERM_BASE)
                .map_err(|_| "CB function id exceeds usize".to_string())?
        } else {
            usize::try_from((raw - crate::calc::COMP_BASE) >> bits)
                .map_err(|_| "CB composite function id exceeds usize".to_string())?
        };
        if function >= function_count {
            return Err("CB live function term exceeds its bound".to_string());
        }
        Ok((None, Some(function)))
    };

    let mut referenced_constants = std::collections::BTreeSet::new();
    let mut referenced_functions = std::collections::BTreeSet::new();
    for source in ontology {
        for literal in source
            .get("body")
            .and_then(serde_json::Value::as_array)
            .into_iter()
            .flatten()
            .chain(
                source
                    .get("head")
                    .and_then(serde_json::Value::as_array)
                    .into_iter()
                    .flatten(),
            )
        {
            for field in ["first", "second"] {
                let Some(raw) = literal
                    .get(field)
                    .and_then(serde_json::Value::as_u64)
                    .and_then(|value| u32::try_from(value).ok())
                else {
                    continue;
                };
                let (constant, function) = decode_term(raw)?;
                if let Some(constant) = constant {
                    referenced_constants.insert(constant);
                }
                if let Some(function) = function {
                    referenced_functions.insert(function);
                }
                if raw >= crate::calc::COMP_BASE {
                    let radix = 1u32 << bits;
                    let individual = usize::try_from((raw - crate::calc::COMP_BASE) % radix)
                        .map_err(|_| "CB composite individual id exceeds usize".to_string())?;
                    if individual >= individual_count {
                        return Err("CB live composite individual exceeds its bound".to_string());
                    }
                    referenced_constants.insert(individual);
                }
            }
        }
    }
    let mut structural_slots = Vec::new();
    structural_slots.extend(referenced_constants.into_iter().map(|id| (false, id, 0)));
    for function in referenced_functions {
        for argument in 0..domain_size {
            structural_slots.push((true, function, argument));
        }
    }
    let structural_count = domain_size
        .checked_pow(
            u32::try_from(structural_slots.len())
                .map_err(|_| "CB structural slot count exceeds u32".to_string())?,
        )
        .unwrap_or(usize::MAX)
        .min(257);
    if structural_count > 256 {
        return Ok(None);
    }

    for structural_index in 0..structural_count {
        let mut constants = vec![0usize; individual_count];
        let mut functions = vec![vec![0usize; domain_size]; function_count];
        let mut digits = structural_index;
        for &(is_function, symbol, argument) in &structural_slots {
            let value = digits % domain_size;
            digits /= domain_size;
            if is_function {
                functions[symbol][argument] = value;
            } else {
                constants[symbol] = value;
            }
        }

        let eval_term = |raw: u32, variables: &std::collections::HashMap<u32, usize>| {
            if raw <= crate::calc::X {
                return variables
                    .get(&raw)
                    .copied()
                    .ok_or_else(|| "CB finite grounding omits a variable".to_string());
            }
            if raw < crate::calc::FTERM_BASE {
                return Ok(constants[(raw - crate::calc::X) as usize]);
            }
            if raw < crate::calc::COMP_BASE {
                let function = (raw - crate::calc::FTERM_BASE) as usize;
                let argument = variables
                    .get(&crate::calc::X)
                    .copied()
                    .ok_or_else(|| "CB function term has no central-variable value".to_string())?;
                return Ok(functions[function][argument]);
            }
            let packed = raw - crate::calc::COMP_BASE;
            let radix = 1u32 << bits;
            let function = (packed / radix) as usize;
            let individual = (packed % radix) as usize;
            Ok(functions[function][constants[individual]])
        };

        let mut clauses = Vec::with_capacity(ontology.len() + 2);
        let mut ground_instances = 0usize;
        for source in ontology {
            let body = source
                .get("body")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB live source clause has no body array".to_string())?;
            let head = source
                .get("head")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB live source clause has no head array".to_string())?;
            let mut variable_ids = std::collections::BTreeSet::new();
            for literal in body.iter().chain(head) {
                for field in ["first", "second"] {
                    if let Some(raw) = literal
                        .get(field)
                        .and_then(serde_json::Value::as_u64)
                        .and_then(|value| u32::try_from(value).ok())
                        .filter(|&raw| raw <= crate::calc::X)
                    {
                        variable_ids.insert(raw);
                    }
                }
            }
            let variable_ids: Vec<u32> = variable_ids.into_iter().collect();
            let valuation_count = domain_size
                .checked_pow(
                    u32::try_from(variable_ids.len())
                        .map_err(|_| "CB variable count exceeds u32".to_string())?,
                )
                .unwrap_or(usize::MAX);
            ground_instances = ground_instances.saturating_add(valuation_count);
            if ground_instances > 5_000 {
                return Ok(None);
            }
            for valuation_index in 0..valuation_count {
                let mut values = valuation_index;
                let variables: std::collections::HashMap<u32, usize> = variable_ids
                    .iter()
                    .map(|&raw| {
                        let value = values % domain_size;
                        values /= domain_size;
                        (raw, value)
                    })
                    .collect();
                let mut clause = Vec::with_capacity(body.len() + head.len());
                let mut tautology = false;
                let mut push_literal =
                    |literal: &serde_json::Value, positive: bool| -> Result<(), String> {
                        let kind = literal
                            .get("kind")
                            .and_then(serde_json::Value::as_str)
                            .ok_or_else(|| "CB live literal has no kind".to_string())?;
                        let first = literal
                            .get("first")
                            .and_then(serde_json::Value::as_u64)
                            .and_then(|value| u32::try_from(value).ok())
                            .ok_or_else(|| "CB live literal has no first term".to_string())?;
                        let first = eval_term(first, &variables)?;
                        let truth_atom = match kind {
                            "concept" => {
                                let iri = literal
                                    .get("iri")
                                    .and_then(serde_json::Value::as_u64)
                                    .and_then(|value| usize::try_from(value).ok())
                                    .ok_or_else(|| "CB concept literal has no iri".to_string())?;
                                if iri >= concept_count {
                                    return Err("CB live concept literal exceeds its bound".to_string());
                                }
                                Some(iri * domain_size + first)
                            }
                            "role" => {
                                let iri = literal
                                    .get("iri")
                                    .and_then(serde_json::Value::as_u64)
                                    .and_then(|value| usize::try_from(value).ok())
                                    .ok_or_else(|| "CB role literal has no iri".to_string())?;
                                if iri >= role_count {
                                    return Err("CB live role literal exceeds its bound".to_string());
                                }
                                let second = literal
                                    .get("second")
                                    .and_then(serde_json::Value::as_u64)
                                    .and_then(|value| u32::try_from(value).ok())
                                    .ok_or_else(|| "CB role literal has no second term".to_string())?;
                                let second = eval_term(second, &variables)?;
                                Some(concept_atoms + iri * role_width + first * domain_size + second)
                            }
                            "equality" | "inequality" => {
                                let second = literal
                                    .get("second")
                                    .and_then(serde_json::Value::as_u64)
                                    .and_then(|value| u32::try_from(value).ok())
                                    .ok_or_else(|| format!("CB {kind} literal has no second term"))?;
                                let equal = first == eval_term(second, &variables)?;
                                let true_now = if kind == "equality" { equal } else { !equal };
                                if true_now == positive {
                                    tautology = true;
                                }
                                None
                            }
                            other => return Err(format!("unsupported CB live literal kind {other}")),
                        };
                        if let Some(atom) = truth_atom {
                            let encoded = i32::try_from(atom + 1)
                                .map_err(|_| "CB finite atom id exceeds i32".to_string())?;
                            clause.push(if positive { encoded } else { -encoded });
                        }
                        Ok(())
                    };
                for literal in body {
                    push_literal(literal, false)?;
                }
                for literal in head {
                    push_literal(literal, true)?;
                }
                if tautology {
                    continue;
                }
                clause.sort_unstable();
                clause.dedup();
                if clause.windows(2).any(|pair| pair[0] == -pair[1]) {
                    continue;
                }
                clauses.push(clause);
            }
        }
        clauses.push(vec![i32::try_from(sub * domain_size + 1)
            .map_err(|_| "CB query concept atom exceeds i32".to_string())?]);
        clauses.push(vec![-i32::try_from(sup * domain_size + 1)
            .map_err(|_| "CB query superclass atom exceeds i32".to_string())?]);
        let Some(assignment) = cb_dpll(&clauses, atom_count) else {
            continue;
        };
        let concepts: Vec<Vec<bool>> = (0..concept_count)
            .map(|concept| {
                (0..domain_size)
                    .map(|element| assignment[concept * domain_size + element] > 0)
                    .collect()
            })
            .collect();
        let roles: Vec<Vec<Vec<bool>>> = (0..role_count)
            .map(|role| {
                (0..domain_size)
                    .map(|source| {
                        (0..domain_size)
                            .map(|target| {
                                assignment[concept_atoms
                                    + role * role_width
                                    + source * domain_size
                                    + target]
                                    > 0
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        return Ok(Some(serde_json::json!({
            "domain_size": domain_size,
            "concepts": concepts,
            "roles": roles,
            "constants": constants,
            "functions": functions,
        })));
    }
    Ok(None)
}

fn cb_one_element_countermodel(
    live_state: &serde_json::Value,
    sub: usize,
    sup: usize,
) -> Result<Option<serde_json::Value>, String> {
    cb_finite_countermodel(live_state, sub, sup, 1)
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct CbPropClause {
    neg: Vec<usize>,
    pos: Vec<usize>,
}

fn cb_blocked_taxonomy_countermodel(
    live_publication: &serde_json::Value,
    sub: usize,
    sup: usize,
) -> Result<Option<serde_json::Value>, String> {
    let live_state = live_publication
        .pointer("/derivation/production_bound/live_state")
        .ok_or_else(|| "live CB publication has no production live state".to_string())?;
    let count = |field: &str| -> Result<usize, String> {
        live_state
            .get(field)
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| format!("CB live state has no numeric {field}"))
    };
    let concept_count = count("concept_count")?;
    let role_count = count("role_count")?;
    let saturation = live_publication
        .pointer(
            "/derivation/production_bound/global_model/blocked_saturation/saturation",
        )
        .ok_or_else(|| "live CB publication has no blocked saturation".to_string())?;
    let atom_count = saturation
        .get("atom_count")
        .and_then(serde_json::Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| "blocked CB saturation has no atom_count".to_string())?;
    let roles_and_equality = role_count
        .checked_add(1)
        .ok_or_else(|| "blocked CB role count overflow".to_string())?;
    let mut carrier_count = 1usize;
    loop {
        let represented_atoms = concept_count
            .checked_mul(carrier_count)
            .and_then(|concepts| {
                carrier_count
                    .checked_mul(carrier_count)
                    .and_then(|square| roles_and_equality.checked_mul(square))
                    .and_then(|binary| concepts.checked_add(binary))
            })
            .ok_or_else(|| "blocked CB carrier-size calculation overflow".to_string())?;
        if represented_atoms == atom_count {
            break;
        }
        if represented_atoms > atom_count {
            return Err("blocked CB atom count has no compatible carrier size".to_string());
        }
        carrier_count = carrier_count
            .checked_add(1)
            .ok_or_else(|| "blocked CB carrier size overflow".to_string())?;
    }
    if sub >= concept_count || sup >= concept_count {
        return Err("blocked CB taxonomy coordinate exceeds the concept bound".to_string());
    }
    let decode_clause = |wire: &serde_json::Value| -> Result<CbPropClause, String> {
        let decode_side = |field: &str| -> Result<Vec<usize>, String> {
            let values = wire
                .get(field)
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| format!("blocked CB clause has no {field} array"))?;
            let mut side = Vec::with_capacity(values.len());
            for value in values {
                let atom = value
                    .as_u64()
                    .and_then(|value| usize::try_from(value).ok())
                    .ok_or_else(|| format!("blocked CB clause has nonnumeric {field} atom"))?;
                if atom >= atom_count {
                    return Err("blocked CB clause atom exceeds atom_count".to_string());
                }
                side.push(atom);
            }
            let before = side.len();
            side.sort_unstable();
            side.dedup();
            if side.len() != before {
                return Err("blocked CB clause side contains a duplicate atom".to_string());
            }
            Ok(side)
        };
        Ok(CbPropClause {
            neg: decode_side("neg")?,
            pos: decode_side("pos")?,
        })
    };
    let premise_values = saturation
        .get("premises")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "blocked CB saturation has no premises array".to_string())?;
    if premise_values.len() > 4094 {
        return Ok(None);
    }
    let mut premises: Vec<CbPropClause> = premise_values
        .iter()
        .map(decode_clause)
        .collect::<Result<_, _>>()?;
    let witness = 0usize;
    let sub_atom = sub
        .checked_mul(carrier_count)
        .and_then(|base| base.checked_add(witness))
        .ok_or_else(|| "blocked CB subclass atom overflow".to_string())?;
    let sup_atom = sup
        .checked_mul(carrier_count)
        .and_then(|base| base.checked_add(witness))
        .ok_or_else(|| "blocked CB superclass atom overflow".to_string())?;
    premises.push(CbPropClause {
        neg: Vec::new(),
        pos: vec![sub_atom],
    });
    premises.push(CbPropClause {
        neg: vec![sup_atom],
        pos: Vec::new(),
    });

    let mut clauses = premises.clone();
    let mut seen: std::collections::BTreeSet<CbPropClause> =
        clauses.iter().cloned().collect();
    let mut trace: Vec<serde_json::Value> = premises
        .iter()
        .enumerate()
        .map(|(index, clause)| {
            serde_json::json!({
                "clause": {"neg": clause.neg, "pos": clause.pos},
                "justification": {"premise": {"index": index}},
            })
        })
        .collect();
    let mut attempts = 0usize;
    let mut changed = true;
    while changed {
        changed = false;
        let round_len = clauses.len();
        for positive in 0..round_len {
            for negative in 0..round_len {
                let pivots: Vec<usize> = clauses[positive]
                    .pos
                    .iter()
                    .copied()
                    .filter(|atom| clauses[negative].neg.binary_search(atom).is_ok())
                    .collect();
                for atom in pivots {
                    attempts += 1;
                    if attempts > 2_000_000 || clauses.len() >= 4096 {
                        return Ok(None);
                    }
                    let mut neg = clauses[positive].neg.clone();
                    neg.extend(
                        clauses[negative]
                            .neg
                            .iter()
                            .copied()
                            .filter(|&candidate| candidate != atom),
                    );
                    neg.sort_unstable();
                    neg.dedup();
                    let mut pos: Vec<usize> = clauses[positive]
                        .pos
                        .iter()
                        .copied()
                        .filter(|&candidate| candidate != atom)
                        .collect();
                    pos.extend(clauses[negative].pos.iter().copied());
                    pos.sort_unstable();
                    pos.dedup();
                    let resolvent = CbPropClause { neg, pos };
                    if resolvent.neg.is_empty() && resolvent.pos.is_empty() {
                        return Ok(None);
                    }
                    if seen.insert(resolvent.clone()) {
                        let clause_index = clauses.len();
                        clauses.push(resolvent.clone());
                        trace.push(serde_json::json!({
                            "clause": {"neg": resolvent.neg, "pos": resolvent.pos},
                            "justification": {"resolve": {
                                "positive": positive,
                                "negative": negative,
                                "atom": atom,
                            }},
                        }));
                        debug_assert_eq!(clause_index, trace.len() - 1);
                        changed = true;
                    }
                }
            }
        }
    }
    let premise_json: Vec<serde_json::Value> = premises
        .iter()
        .map(|clause| serde_json::json!({"neg": clause.neg, "pos": clause.pos}))
        .collect();
    Ok(Some(serde_json::json!({
        "version": 1,
        "witness": witness,
        "saturation": {
            "version": 1,
            "atom_count": atom_count,
            "premises": premise_json,
            "trace": trace,
        },
    })))
}

/// Canonically decompose every finite source role chain into binary rules.
/// Source role ids retain their numeric identity; fresh intermediate roles are
/// allocated consecutively above `source_role_count`. The returned derivation
/// trees use the exact externally-tagged JSON shape checked by Lean's
/// `CBRoleChainBinaryDerivationWire`.
fn cb_canonical_binary_role_chains(
    source_role_count: usize,
    chains: &[(Vec<usize>, usize)],
) -> Result<(usize, Vec<serde_json::Value>, Vec<serde_json::Value>), String> {
    fn atom(role: usize) -> serde_json::Value {
        serde_json::json!({"atom": {"role": role}})
    }

    fn identity(
        body: &[usize],
        next_role: &mut usize,
        rules: &mut Vec<serde_json::Value>,
    ) -> Result<(usize, serde_json::Value), String> {
        let (&first, rest) = body
            .split_first()
            .ok_or_else(|| "canonical binary identity received an empty path".to_string())?;
        if rest.is_empty() {
            return Ok((first, atom(first)));
        }
        let (right_role, right) = identity(rest, next_role, rules)?;
        let result = *next_role;
        *next_role = next_role
            .checked_add(1)
            .ok_or_else(|| "canonical binary fresh-role count overflow".to_string())?;
        let rule = rules.len();
        rules.push(serde_json::json!({
            "first": first,
            "second": right_role,
            "conclusion": result,
        }));
        Ok((
            result,
            serde_json::json!({"compose": {
                "left": atom(first),
                "right": right,
                "rule": rule,
            }}),
        ))
    }

    let mut next_role = source_role_count;
    let mut rules = Vec::new();
    let mut derivations = Vec::with_capacity(chains.len());
    for (body, sup) in chains {
        if body.len() < 2 {
            return Err("OWL property chain has fewer than two body roles".to_string());
        }
        if *sup >= source_role_count || body.iter().any(|role| *role >= source_role_count) {
            return Err("OWL property chain role exceeds the source role bound".to_string());
        }
        let first = body[0];
        let (right_role, right) = identity(&body[1..], &mut next_role, &mut rules)?;
        let rule = rules.len();
        rules.push(serde_json::json!({
            "first": first,
            "second": right_role,
            "conclusion": sup,
        }));
        derivations.push(serde_json::json!({"compose": {
            "left": atom(first),
            "right": right,
            "rule": rule,
        }}));
    }
    Ok((next_role, rules, derivations))
}

#[derive(Debug, Clone, PartialEq)]
struct CbRegularArbitraryChainSource {
    concept_count: usize,
    role_count: usize,
    function_count: usize,
    individual_count: usize,
    source_binding: serde_json::Value,
    source_clauses: Vec<serde_json::Value>,
    source_ontology: Vec<serde_json::Value>,
    clauses: Vec<serde_json::Value>,
    chains: Vec<serde_json::Value>,
}

/// Recover the exact typed source carried by the already checked production
/// certificate and translate it to the safe-source wire used by the strongest
/// CB regular countermodel.  The global certificate repeats its production run
/// under several closure branches.  Requiring every encountered source binding
/// to agree prevents this adapter from selecting a convenient but unrelated
/// copy.
fn cb_regular_arbitrary_chain_source(
    global_model: &serde_json::Value,
) -> Result<CbRegularArbitraryChainSource, String> {
    fn collect<'a>(value: &'a serde_json::Value, found: &mut Vec<&'a serde_json::Value>) {
        match value {
            serde_json::Value::Object(object) => {
                if object.contains_key("source_clauses")
                    && object.contains_key("role_chains")
                    && object.contains_key("ontology")
                    && object.contains_key("concept_count")
                    && object.contains_key("role_count")
                    && object.contains_key("individual_count")
                {
                    found.push(value);
                }
                for child in object.values() {
                    collect(child, found);
                }
            }
            serde_json::Value::Array(array) => {
                for child in array {
                    collect(child, found);
                }
            }
            _ => {}
        }
    }

    fn count(source: &serde_json::Value, field: &str) -> Result<usize, String> {
        source
            .get(field)
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| format!("certified CB source has no numeric {field}"))
    }

    fn translate_clause(clause: &serde_json::Value) -> Result<serde_json::Value, String> {
        let object = clause
            .as_object()
            .ok_or_else(|| "certified CB source clause is not an object".to_string())?;
        if object.len() != 1 {
            return Err("certified CB source clause has an ambiguous constructor".to_string());
        }
        let (kind, payload) = object.iter().next().expect("one source constructor");
        let base = |kind: &str, payload: &serde_json::Value| {
            let mut constructor = serde_json::Map::new();
            constructor.insert(kind.to_string(), payload.clone());
            serde_json::json!({"core": {"clause": {"base": {"clause":
                serde_json::Value::Object(constructor)}}}})
        };
        match kind.as_str() {
            "gci" | "exR" | "allR" | "exL" => Ok(base(kind, payload)),
            "subR" => Ok(base(
                "subR",
                &serde_json::json!({
                    "premise": payload.get("sub").ok_or_else(||
                        "subR source clause has no sub role".to_string())?,
                    "conclusion": payload.get("sup").ok_or_else(||
                        "subR source clause has no super role".to_string())?,
                }),
            )),
            "inverse" => Ok(base("inv", payload)),
            "nominal" => Ok(serde_json::json!({"core": {"clause": {"nominal": {
                "clause": payload
            }}}})),
            "functional" => {
                let role = payload
                    .get("role")
                    .and_then(serde_json::Value::as_u64)
                    .ok_or_else(|| "functional source clause has no role".to_string())?;
                Ok(serde_json::json!({"func": {"role": role}}))
            }
            "atMost" => {
                let field = |name: &str| {
                    payload
                        .get(name)
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| format!("atMost source clause has no {name}"))
                };
                Ok(serde_json::json!({"atMost": {
                    "bound": field("cardinality")?,
                    "role": field("role")?,
                    "filler": field("concept")?,
                }}))
            }
            "guardedAtMost" => {
                let field = |name: &str| {
                    payload
                        .get(name)
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| format!("guardedAtMost source clause has no {name}"))
                };
                Ok(serde_json::json!({"guardedAtMost": {
                    "marker": field("source")?,
                    "bound": field("cardinality")?,
                    "role": field("role")?,
                    "filler": field("concept")?,
                }}))
            }
            "guardedAtLeast" => {
                let field = |name: &str| {
                    payload
                        .get(name)
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| format!("guardedAtLeast source clause has no {name}"))
                };
                Ok(serde_json::json!({"atLeast": {
                    "marker": field("source")?,
                    "bound": field("cardinality")?,
                    "role": field("role")?,
                    "filler": field("concept")?,
                }}))
            }
            other => Err(format!("unsupported certified CB source constructor {other}")),
        }
    }

    let mut bindings = Vec::new();
    collect(global_model, &mut bindings);
    let first = bindings
        .first()
        .copied()
        .ok_or_else(|| "CB global model has no typed source binding".to_string())?;
    for binding in bindings.iter().skip(1) {
        if *binding != first {
            return Err("CB global model contains disagreeing typed source bindings".to_string());
        }
    }
    let source_clauses = first
        .get("source_clauses")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "certified CB source has no source_clauses array".to_string())?;
    let clauses = source_clauses
        .iter()
        .map(translate_clause)
        .collect::<Result<Vec<_>, _>>()?;
    let chains = first
        .get("role_chains")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| "certified CB source has no role_chains array".to_string())?;
    let source_ontology = first
        .get("ontology")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| "certified CB source has no ontology array".to_string())?;
    Ok(CbRegularArbitraryChainSource {
        concept_count: count(first, "concept_count")?,
        role_count: count(first, "role_count")?,
        function_count: count(first, "function_count")?,
        individual_count: count(first, "individual_count")?,
        source_binding: first.clone(),
        source_clauses: source_clauses.clone(),
        source_ontology,
        clauses,
        chains,
    })
}

fn cb_regular_arbitrary_chain_countermodel(
    source: &CbRegularArbitraryChainSource,
    sub: usize,
    sup: usize,
) -> Result<Option<serde_json::Value>, String> {
    use crate::tableau::{Atom, Clause, CLit};

    let numeric = |value: u64, kind: &str| -> Result<u32, String> {
        u32::try_from(value).map_err(|_| format!("{kind} id exceeds the HT numeric bound"))
    };
    let field = |payload: &serde_json::Value, name: &str| -> Result<u64, String> {
        payload
            .get(name)
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| format!("certified CB source constructor has no numeric {name}"))
    };
    let concept = |payload: &serde_json::Value, name: &str| -> Result<u32, String> {
        let raw = field(payload, name)?;
        let mapped = raw
            .checked_add(1)
            .ok_or_else(|| "CB concept-map successor overflow".to_string())?;
        numeric(mapped, "concept")
    };
    let role = |payload: &serde_json::Value, name: &str| -> Result<u32, String> {
        numeric(field(payload, name)?, "role")
    };
    let pos = |concept, term| Atom::Concept {
        lit: CLit::pos(concept),
        t: term,
    };

    if sub >= source.concept_count || sup >= source.concept_count {
        return Err("CB regular query exceeds the certified source signature".to_string());
    }
    let chain_pairs = source
        .chains
        .iter()
        .map(|chain| {
            let body = chain
                .get("body")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "certified role chain has no body".to_string())?
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .and_then(|value| usize::try_from(value).ok())
                        .ok_or_else(|| "certified role chain body is not numeric".to_string())
                })
                .collect::<Result<Vec<_>, _>>()?;
            let sup = chain
                .get("sup")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| "certified role chain has no super-role".to_string())?;
            Ok((body, sup))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let (target_role_count, binary_chains, chain_derivations) =
        cb_canonical_binary_role_chains(source.role_count, &chain_pairs)?;

    let mut clauses = Vec::new();
    let mut cardinality_defs = Vec::new();
    let mut nominal_proxies: Vec<Vec<u32>> = vec![Vec::new(); source.individual_count];
    for clause in &source.source_clauses {
        let object = clause
            .as_object()
            .ok_or_else(|| "certified source clause is not an object".to_string())?;
        let (kind, payload) = object
            .iter()
            .next()
            .ok_or_else(|| "certified source clause has no constructor".to_string())?;
        match kind.as_str() {
            "gci" => {
                let concepts = |name: &str| -> Result<Vec<u32>, String> {
                    payload
                        .get(name)
                        .and_then(serde_json::Value::as_array)
                        .ok_or_else(|| format!("gci source clause has no {name}"))?
                        .iter()
                        .map(|value| {
                            let raw = value
                                .as_u64()
                                .ok_or_else(|| "gci concept is not numeric".to_string())?;
                            numeric(
                                raw.checked_add(1)
                                    .ok_or_else(|| "gci concept-map overflow".to_string())?,
                                "concept",
                            )
                        })
                        .collect()
                };
                clauses.push(Clause::new(
                    concepts("body")?.into_iter().map(|c| pos(c, 0)).collect(),
                    concepts("head")?.into_iter().map(|c| pos(c, 0)).collect(),
                ));
            }
            "exR" => clauses.push(Clause::new(
                vec![pos(concept(payload, "source")?, 0)],
                vec![Atom::Exists {
                    r: role(payload, "role")?,
                    fil: CLit::pos(concept(payload, "filler")?),
                    t: 0,
                }],
            )),
            "allR" => clauses.push(Clause::new(
                vec![
                    pos(concept(payload, "source")?, 0),
                    Atom::Role {
                        r: role(payload, "role")?,
                        s: 0,
                        t: 2,
                    },
                ],
                vec![pos(concept(payload, "filler")?, 2)],
            )),
            "exL" => clauses.push(Clause::new(
                vec![
                    Atom::Role {
                        r: role(payload, "role")?,
                        s: 0,
                        t: 2,
                    },
                    pos(concept(payload, "filler")?, 2),
                ],
                vec![pos(concept(payload, "conclusion")?, 0)],
            )),
            "subR" => clauses.push(Clause::new(
                vec![Atom::Role {
                    r: role(payload, "sub")?,
                    s: 0,
                    t: 2,
                }],
                vec![Atom::Role {
                    r: role(payload, "sup")?,
                    s: 0,
                    t: 2,
                }],
            )),
            "inverse" => {
                let first = role(payload, "role")?;
                let second = role(payload, "inverse")?;
                clauses.push(Clause::new(
                    vec![Atom::Role {
                        r: first,
                        s: 0,
                        t: 2,
                    }],
                    vec![Atom::Role {
                        r: second,
                        s: 2,
                        t: 0,
                    }],
                ));
                clauses.push(Clause::new(
                    vec![Atom::Role {
                        r: second,
                        s: 0,
                        t: 2,
                    }],
                    vec![Atom::Role {
                        r: first,
                        s: 2,
                        t: 0,
                    }],
                ));
            }
            "functional" => {
                cardinality_defs.push((
                    0,
                    false,
                    1,
                    role(payload, "role")?,
                    0,
                    false,
                ));
                clauses.push(Clause::new(Vec::new(), vec![pos(0, 0)]));
                clauses.push(Clause::new(Vec::new(), vec![pos(0, 0)]));
            }
            "atMost" => {
                cardinality_defs.push((
                    0,
                    false,
                    u32::try_from(field(payload, "cardinality")?)
                        .map_err(|_| "atMost bound exceeds u32".to_string())?,
                    role(payload, "role")?,
                    concept(payload, "concept")?,
                    false,
                ));
                clauses.push(Clause::new(Vec::new(), vec![pos(0, 0)]));
            }
            "guardedAtMost" => {
                cardinality_defs.push((
                    concept(payload, "source")?,
                    false,
                    u32::try_from(field(payload, "cardinality")?)
                        .map_err(|_| "guardedAtMost bound exceeds u32".to_string())?,
                    role(payload, "role")?,
                    concept(payload, "concept")?,
                    false,
                ));
            }
            "guardedAtLeast" => {
                cardinality_defs.push((
                    concept(payload, "source")?,
                    true,
                    u32::try_from(field(payload, "cardinality")?)
                        .map_err(|_| "guardedAtLeast bound exceeds u32".to_string())?,
                    role(payload, "role")?,
                    concept(payload, "concept")?,
                    false,
                ));
            }
            "nominal" => {
                let individual: usize = field(payload, "individual")?
                    .try_into()
                    .map_err(|_| "nominal individual exceeds usize".to_string())?;
                let proxies = nominal_proxies
                    .get_mut(individual)
                    .ok_or_else(|| "nominal individual exceeds the source bound".to_string())?;
                proxies.push(concept(payload, "concept")?);
            }
            other => return Err(format!("unsupported certified source constructor {other}")),
        }
    }
    for binary in &binary_chains {
        let value = |name: &str| -> Result<u32, String> {
            numeric(
                binary
                    .get(name)
                    .and_then(serde_json::Value::as_u64)
                    .ok_or_else(|| format!("binary role chain has no {name}"))?,
                "binary-chain role",
            )
        };
        clauses.push(Clause::new(
            vec![
                Atom::Role {
                    r: value("first")?,
                    s: 0,
                    t: 1,
                },
                Atom::Role {
                    r: value("second")?,
                    s: 1,
                    t: 2,
                },
            ],
            vec![Atom::Role {
                r: value("conclusion")?,
                s: 0,
                t: 2,
            }],
        ));
    }

    let mut tableau = crate::tableau::hypertableau::Ht::new_certified(clauses);
    if !cardinality_defs.is_empty() {
        tableau.set_certification_card_defs_raw(&cardinality_defs);
    }
    if source.individual_count != 0 {
        let nominals = nominal_proxies.iter().flatten().copied().collect();
        tableau.set_nominals(nominals);
        tableau.set_native_abox(
            nominal_proxies
                .iter()
                .cloned()
                .map(|proxies| (proxies, Vec::new()))
                .collect(),
            Vec::new(),
            Vec::new(),
        );
    }
    tableau.set_certificate_signature_floor(
        source.concept_count + 1,
        target_role_count,
        3,
    );
    let anchored = tableau.lean_cb_anchored_cardinality_countermodel_json(
        u32::try_from(sub + 1).map_err(|_| "subclass id exceeds u32".to_string())?,
        u32::try_from(sup + 1).map_err(|_| "superclass id exceeds u32".to_string())?,
    )?;
    anchored
        .map(|anchored| {
            let individual_roots = (0..source.individual_count)
                .map(|individual| {
                    anchored
                        .pointer(&format!("/anchored/class_map/{}", individual + 1))
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| {
                            "anchored countermodel omits an individual root class".to_string()
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(serde_json::json!({
                "version": 1,
                "clauses": source.clauses,
                "chains": source.chains,
                "target_role_count": target_role_count,
                "binary_chains": binary_chains,
                "chain_derivations": chain_derivations,
                "individual_roots": individual_roots,
                "anchored": anchored,
            }))
        })
        .transpose()
}

fn cb_remap_production_trace_index(
    raw: usize,
    prior_terminals: &[usize],
    local_base: usize,
    local_len: usize,
    current_local: usize,
) -> Result<usize, String> {
    if let Some(&mapped) = prior_terminals.get(raw) {
        return Ok(mapped);
    }
    let local = raw
        .checked_sub(prior_terminals.len())
        .ok_or_else(|| "CB production trace index underflow".to_string())?;
    if local >= local_len || local >= current_local {
        return Err("CB production trace contains a forward or out-of-range reference".to_string());
    }
    Ok(local_base + local)
}

fn cb_decode_live_clause_json(
    value: &serde_json::Value,
) -> Result<crate::engine::CbLiveClause, String> {
    let decode_literal = |value: &serde_json::Value| -> Result<crate::engine::CbLiveLit, String> {
        let kind = match value
            .get("kind")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "CB live literal has no kind".to_string())?
        {
            "concept" => "concept",
            "role" => "role",
            "equality" => "equality",
            "inequality" => "inequality",
            other => return Err(format!("unsupported CB live literal kind {other}")),
        };
        let numeric = |field: &str| -> Result<u32, String> {
            value
                .get(field)
                .and_then(serde_json::Value::as_u64)
                .and_then(|raw| u32::try_from(raw).ok())
                .ok_or_else(|| format!("CB live literal has no numeric {field}"))
        };
        let optional = |field: &str| -> Result<Option<u32>, String> {
            match value.get(field) {
                None | Some(serde_json::Value::Null) => Ok(None),
                Some(_) => numeric(field).map(Some),
            }
        };
        Ok(crate::engine::CbLiveLit {
            kind,
            iri: optional("iri")?,
            first: numeric("first")?,
            second: optional("second")?,
        })
    };
    let decode_side = |name: &str| -> Result<Vec<crate::engine::CbLiveLit>, String> {
        value
            .get(name)
            .and_then(serde_json::Value::as_array)
            .ok_or_else(|| format!("CB live clause has no {name}"))?
            .iter()
            .map(decode_literal)
            .collect()
    };
    Ok(crate::engine::CbLiveClause {
        body: decode_side("body")?,
        head: decode_side("head")?,
    })
}

fn cb_remap_production_justification(
    justification: &serde_json::Value,
    prior_terminals: &[usize],
    local_base: usize,
    local_len: usize,
    current_local: usize,
) -> Result<serde_json::Value, String> {
    let mut result = justification.clone();
    let object = result
        .as_object_mut()
        .ok_or_else(|| "CB production justification is not an object".to_string())?;
    let Some((kind, payload)) = object.iter_mut().next() else {
        return Err("CB production justification is empty".to_string());
    };
    let fields: &[&str] = match kind.as_str() {
        "resolve" => &["positive", "negative"],
        "paramodulate" => &["equality", "other"],
        "factor" | "deleteReflexiveInequality" => &["source"],
        "join3" => &["consumer", "provider", "bridge"],
        "premise" | "assumption" | "tautology" => &[],
        other => return Err(format!("unsupported CB production justification {other}")),
    };
    for field in fields {
        let raw = payload
            .get(*field)
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| format!("CB production justification has no numeric {field}"))?;
        payload[*field] = serde_json::json!(cb_remap_production_trace_index(
            raw,
            prior_terminals,
            local_base,
            local_len,
            current_local,
        )?);
    }
    Ok(result)
}

fn cb_standalone_production_trace(
    live_publication: &serde_json::Value,
    terminal_event: usize,
) -> Result<Vec<serde_json::Value>, String> {
    let history = live_publication
        .pointer("/derivation/production_bound/live_state/insertion_history")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no insertion history".to_string())?;
    let evidence = live_publication
        .pointer("/derivation/insertion_evidence")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no insertion evidence".to_string())?;
    let live_state = live_publication
        .pointer("/derivation/production_bound/live_state")
        .ok_or_else(|| "live CB publication has no live state".to_string())?;
    if history.len() != evidence.len() {
        return Err("CB insertion history and evidence lengths differ".to_string());
    }

    fn append(
        event_index: usize,
        history: &[serde_json::Value],
        evidence: &[serde_json::Value],
        live_state: &serde_json::Value,
        active: &mut std::collections::BTreeSet<usize>,
        output: &mut Vec<serde_json::Value>,
    ) -> Result<usize, String> {
        if !active.insert(event_index) {
            return Err("CB insertion evidence contains a dependency cycle".to_string());
        }
        let event = history
            .get(event_index)
            .ok_or_else(|| "CB insertion evidence references a missing event".to_string())?;
        let proof = evidence
            .get(event_index)
            .ok_or_else(|| "CB insertion event has no evidence".to_string())?;
        let kind = proof
            .get("kind")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "CB insertion evidence has no kind".to_string())?;
        let result = if kind == "seed" {
            let root = event
                .get("root")
                .and_then(serde_json::Value::as_bool)
                .ok_or_else(|| "CB insertion event has no arena domain".to_string())?;
            let clause_id = event
                .get("clause_id")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| "CB insertion event has no clause id".to_string())?;
            let arena_name = if root {
                "root_clause_arena"
            } else {
                "ordinary_clause_arena"
            };
            let raw_clause = live_state
                .get(arena_name)
                .and_then(serde_json::Value::as_array)
                .and_then(|arena| arena.get(clause_id))
                .cloned()
                .ok_or_else(|| "CB seed event references a missing arena clause".to_string())?;
            let raw_clause = cb_decode_live_clause_json(&raw_clause)?;
            let comp_ind_bits = live_state
                .get("comp_ind_bits")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| u32::try_from(value).ok())
                .ok_or_else(|| "CB live state has no packed-term width".to_string())?;
            let clause = cb_wire_clause(&raw_clause, comp_ind_bits);
            let origin = event
                .get("origin_hint")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "CB seed event has no origin".to_string())?;
            let origin_index = event
                .get("origin_index")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| "CB seed event has no origin index".to_string())?;
            let justification = match origin {
                "core" => serde_json::json!({"assumption": {"index": origin_index}}),
                "ontology_fact" => serde_json::json!({"premise": {
                    "index": origin_index, "substitution": []
                }}),
                other => return Err(format!("unsupported CB seed origin {other}")),
            };
            output.push(serde_json::json!({
                "clause": clause,
                "justification": justification,
            }));
            output.len() - 1
        } else if kind == "local" {
            let prior = proof
                .get("prior_events")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "local CB insertion evidence has no prior events".to_string())?;
            let mut prior_terminals = Vec::with_capacity(prior.len());
            for reference in prior {
                let prior_index = reference
                    .get("event_index")
                    .and_then(serde_json::Value::as_u64)
                    .and_then(|value| usize::try_from(value).ok())
                    .ok_or_else(|| "CB prior-event reference is not numeric".to_string())?;
                if prior_index >= event_index {
                    return Err("CB insertion evidence references a non-earlier event".to_string());
                }
                prior_terminals.push(append(
                    prior_index,
                    history,
                    evidence,
                    live_state,
                    active,
                    output,
                )?);
            }
            let trace = proof
                .get("trace")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "local CB insertion evidence has no trace".to_string())?;
            if trace.is_empty() {
                return Err("local CB insertion evidence has an empty trace".to_string());
            }
            let local_base = output.len();
            for (local_index, entry) in trace.iter().enumerate() {
                let clause = entry
                    .get("clause")
                    .cloned()
                    .ok_or_else(|| "CB local trace entry has no clause".to_string())?;
                let justification = cb_remap_production_justification(
                    entry
                        .get("justification")
                        .ok_or_else(|| "CB local trace entry has no justification".to_string())?,
                    &prior_terminals,
                    local_base,
                    trace.len(),
                    local_index,
                )?;
                output.push(serde_json::json!({
                    "clause": clause,
                    "justification": justification,
                }));
            }
            output.len() - 1
        } else {
            return Err(format!(
                "CB event {event_index} has no standalone production derivation ({kind})"
            ));
        };
        active.remove(&event_index);
        Ok(result)
    }

    let mut output = Vec::new();
    append(
        terminal_event,
        history,
        evidence,
        live_state,
        &mut std::collections::BTreeSet::new(),
        &mut output,
    )?;
    Ok(output)
}

fn cb_wire_live_predicate_json(
    value: &serde_json::Value,
    bits: u32,
) -> Result<serde_json::Value, String> {
    let kind = value
        .get("kind")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "CB live core predicate has no kind".to_string())?;
    let iri = value
        .get("iri")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| "CB live core predicate has no IRI".to_string())?;
    let first = value
        .get("first")
        .and_then(serde_json::Value::as_u64)
        .and_then(|term| u32::try_from(term).ok())
        .ok_or_else(|| "CB live core predicate has no first term".to_string())?;
    match kind {
        "concept" => Ok(serde_json::json!({"concept": {
            "concept": iri,
            "term": cb_wire_term(first, bits),
        }})),
        "role" => {
            let second = value
                .get("second")
                .and_then(serde_json::Value::as_u64)
                .and_then(|term| u32::try_from(term).ok())
                .ok_or_else(|| "CB live role core predicate has no target".to_string())?;
            Ok(serde_json::json!({"role": {
                "role": iri,
                "source": cb_wire_term(first, bits),
                "target": cb_wire_term(second, bits),
            }}))
        }
        other => Err(format!("unsupported CB live core predicate kind {other}")),
    }
}

/// Translate the dependency closure of selected live insertion events to the
/// compact chronological proof DAG checked by `CBStandaloneContextProofWire`.
/// Each live event is emitted at most once, and every edge points to an earlier
/// node. This is the native positive-evidence boundary for nested Pred chains.
fn cb_standalone_context_proof_document(
    live_publication: &serde_json::Value,
    terminal_events: &[usize],
) -> Result<(serde_json::Value, std::collections::HashMap<usize, usize>), String> {
    let global = live_publication
        .pointer("/derivation/production_bound/global_model")
        .ok_or_else(|| "live CB publication has no typed source certificate".to_string())?;
    let source = cb_regular_arbitrary_chain_source(global)?;
    let live = live_publication
        .pointer("/derivation/production_bound/live_state")
        .ok_or_else(|| "live CB publication has no live state".to_string())?;
    let history = live
        .get("insertion_history")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB state has no insertion history".to_string())?;
    let proofs = live_publication
        .pointer("/derivation/insertion_evidence")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no insertion evidence".to_string())?;
    let contexts = live
        .get("contexts")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB state has no contexts".to_string())?;
    let bits = live
        .get("comp_ind_bits")
        .and_then(serde_json::Value::as_u64)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| "live CB state has no packed-term width".to_string())?;
    if history.len() != proofs.len() {
        return Err("CB insertion history and evidence lengths differ".to_string());
    }

    fn reference_index(value: &serde_json::Value, name: &str) -> Result<usize, String> {
        value
            .get("event_index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|index| usize::try_from(index).ok())
            .ok_or_else(|| format!("CB {name} reference has no event index"))
    }

    struct Builder<'a> {
        history: &'a [serde_json::Value],
        proofs: &'a [serde_json::Value],
        contexts: &'a [serde_json::Value],
        live: &'a serde_json::Value,
        bits: u32,
        nodes: Vec<serde_json::Value>,
        event_nodes: std::collections::HashMap<usize, usize>,
        active: std::collections::BTreeSet<usize>,
    }

    impl Builder<'_> {
        fn append(&mut self, event_index: usize) -> Result<usize, String> {
            if let Some(&node) = self.event_nodes.get(&event_index) {
                return Ok(node);
            }
            if !self.active.insert(event_index) {
                return Err("CB standalone context proof contains a dependency cycle".to_string());
            }
            let event = self
                .history
                .get(event_index)
                .ok_or_else(|| "CB standalone proof references a missing event".to_string())?;
            let proof = self
                .proofs
                .get(event_index)
                .ok_or_else(|| "CB standalone proof event has no evidence".to_string())?;
            let context_index = event
                .get("context_index")
                .and_then(serde_json::Value::as_u64)
                .and_then(|index| usize::try_from(index).ok())
                .ok_or_else(|| "CB insertion event has no context index".to_string())?;
            let context = self
                .contexts
                .get(context_index)
                .ok_or_else(|| "CB insertion event references a missing context".to_string())?;
            let root = event
                .get("root")
                .and_then(serde_json::Value::as_bool)
                .ok_or_else(|| "CB insertion event has no arena domain".to_string())?;
            let clause_id = event
                .get("clause_id")
                .and_then(serde_json::Value::as_u64)
                .and_then(|id| usize::try_from(id).ok())
                .ok_or_else(|| "CB insertion event has no clause id".to_string())?;
            let raw_clause = self
                .live
                .get(if root { "root_clause_arena" } else { "ordinary_clause_arena" })
                .and_then(serde_json::Value::as_array)
                .and_then(|arena| arena.get(clause_id))
                .ok_or_else(|| "CB insertion event references a missing arena clause".to_string())?;
            let clause = cb_wire_clause(&cb_decode_live_clause_json(raw_clause)?, self.bits);
            let core = context
                .get("core")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "CB insertion context has no core".to_string())?
                .iter()
                .map(|predicate| cb_wire_live_predicate_json(predicate, self.bits))
                .collect::<Result<Vec<_>, _>>()?;
            let kind = proof
                .get("kind")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "CB insertion evidence has no kind".to_string())?;
            let evidence = match kind {
                "seed" => {
                    let origin = event
                        .get("origin_hint")
                        .and_then(serde_json::Value::as_str)
                        .ok_or_else(|| "CB seed event has no origin".to_string())?;
                    let origin_index = event
                        .get("origin_index")
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| "CB seed event has no origin index".to_string())?;
                    let justification = match origin {
                        "core" => serde_json::json!({"assumption": {"index": origin_index}}),
                        "ontology_fact" => serde_json::json!({"premise": {
                            "index": origin_index, "substitution": []
                        }}),
                        other => return Err(format!("unsupported CB seed origin {other}")),
                    };
                    serde_json::json!({"local": {
                        "prior_nodes": [],
                        "trace": [{"clause": clause.clone(), "justification": justification}],
                    }})
                }
                "local" => {
                    let references = proof
                        .get("prior_events")
                        .and_then(serde_json::Value::as_array)
                        .ok_or_else(|| "local CB evidence has no prior events".to_string())?;
                    let mut prior_nodes = Vec::with_capacity(references.len());
                    for reference in references {
                        let dependency = reference_index(reference, "local premise")?;
                        if dependency >= event_index {
                            return Err("local CB evidence references a non-earlier event".to_string());
                        }
                        prior_nodes.push(self.append(dependency)?);
                    }
                    let trace = proof
                        .get("trace")
                        .and_then(serde_json::Value::as_array)
                        .cloned()
                        .ok_or_else(|| "local CB evidence has no trace".to_string())?;
                    serde_json::json!({"local": {
                        "prior_nodes": prior_nodes,
                        "trace": trace,
                    }})
                }
                "pred" => {
                    let sender = reference_index(
                        proof.get("sender_event").ok_or_else(||
                            "CB Pred evidence has no sender".to_string())?,
                        "Pred sender",
                    )?;
                    if sender >= event_index {
                        return Err("CB Pred sender is not earlier".to_string());
                    }
                    let sender_node = self.append(sender)?;
                    let mut provider_nodes = Vec::new();
                    for provider in proof
                        .get("provider_events")
                        .and_then(serde_json::Value::as_array)
                        .ok_or_else(|| "CB Pred evidence has no providers".to_string())?
                    {
                        let dependency = reference_index(provider, "Pred provider")?;
                        if dependency >= event_index {
                            return Err("CB Pred provider is not earlier".to_string());
                        }
                        provider_nodes.push(self.append(dependency)?);
                    }
                    serde_json::json!({"pred": {
                        "sender_node": sender_node,
                        "provider_nodes": provider_nodes,
                        "edge_label": proof.get("edge_label").cloned().ok_or_else(||
                            "CB Pred evidence has no edge label".to_string())?,
                        "payload": proof.get("payload").cloned().ok_or_else(||
                            "CB Pred evidence has no payload".to_string())?,
                        "matched": proof.get("matched_predicates").cloned().ok_or_else(||
                            "CB Pred evidence has no matched predicates".to_string())?,
                    }})
                }
                other => return Err(format!(
                    "CB event {event_index} has no chronological proof ({other})"
                )),
            };
            let node_index = self.nodes.len();
            self.nodes.push(serde_json::json!({
                "core": core,
                "clause": clause,
                "evidence": evidence,
            }));
            self.event_nodes.insert(event_index, node_index);
            self.active.remove(&event_index);
            Ok(node_index)
        }
    }

    let mut builder = Builder {
        history,
        proofs,
        contexts,
        live,
        bits,
        nodes: Vec::new(),
        event_nodes: std::collections::HashMap::new(),
        active: std::collections::BTreeSet::new(),
    };
    for &event in terminal_events {
        builder.append(event)?;
    }
    let document = serde_json::json!({
        "version": 1,
        "concept_count": source.concept_count,
        "role_count": source.role_count,
        "function_count": source.function_count,
        "individual_count": source.individual_count,
        "ontology": source.source_ontology,
        "proof": {"version": 1, "nodes": builder.nodes},
    });
    Ok((document, builder.event_nodes))
}

fn cb_public_witness_events(
    live_publication: &serde_json::Value,
) -> Result<Vec<usize>, String> {
    let live_unit_clause = |concept: usize| {
        serde_json::json!({"body": [], "head": [{
            "kind": "concept", "iri": concept,
            "first": crate::calc::X, "second": null
        }]})
    };
    let mut events = Vec::new();
    for positive in live_publication
        .get("public_subsumptions")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no public subsumptions".to_string())?
    {
        let context = positive
            .get("context_index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "positive CB witness has no context index".to_string())?;
        let sup = positive
            .get("sup")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "positive CB witness has no superclass".to_string())?;
        events.push(cb_live_terminal_event_for_clause(
            live_publication,
            context,
            &live_unit_clause(sup),
        )?);
    }
    let empty = serde_json::json!({"body": [], "head": []});
    for unsatisfiable in live_publication
        .get("unsatisfiable")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no unsatisfiable rows".to_string())?
    {
        let context = unsatisfiable
            .get("context_index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "unsatisfiable CB witness has no context index".to_string())?;
        events.push(cb_live_terminal_event_for_clause(
            live_publication,
            context,
            &empty,
        )?);
    }
    events.sort_unstable();
    events.dedup();
    Ok(events)
}

/// Build the exact row-major matrix around an already checked live publication.
/// Positive, reflexive, and bottom-implied cells are complete immediately.
/// Omitted cells remain explicit `unresolved` evidence and are rejected by the
/// Lean exact checker until a finite or regular countermodel producer fills
/// them. This diagnostic artifact measures the real remaining obligation.
fn cb_exact_taxonomy_candidate(
    live_publication: &serde_json::Value,
) -> Result<(serde_json::Value, usize), String> {
    let live_state = live_publication
        .pointer("/derivation/production_bound/live_state")
        .ok_or_else(|| "live CB publication has no production live state".to_string())?;
    let rows = live_publication
        .get("public_rows")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no public_rows array".to_string())?;
    let positives = live_publication
        .get("public_subsumptions")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no public_subsumptions array".to_string())?;
    let unsatisfiable = live_publication
        .get("unsatisfiable")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no unsatisfiable array".to_string())?;
    let regular_source = live_publication
        .pointer("/derivation/production_bound/global_model")
        .map(cb_regular_arbitrary_chain_source)
        .transpose()?;
    let regular_countermodel = |sub, sup| match regular_source.as_ref() {
        Some(source) => cb_regular_arbitrary_chain_countermodel(source, sub, sup),
        None => Ok(None),
    };

    let mut named = Vec::with_capacity(rows.len());
    for row in rows {
        let sub = row
            .get("sub")
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| "live CB public row has no numeric subject".to_string())?;
        let sub = usize::try_from(sub)
            .map_err(|_| "live CB public row subject exceeds usize".to_string())?;
        if named.contains(&sub) {
            return Err("live CB public rows contain a duplicate subject".to_string());
        }
        named.push(sub);
    }

    let mut positive_index = std::collections::HashMap::new();
    for (index, cell) in positives.iter().enumerate() {
        let sub = cell
            .get("sub")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live CB positive cell has no numeric subclass".to_string())?;
        let sup = cell
            .get("sup")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live CB positive cell has no numeric superclass".to_string())?;
        if positive_index.insert((sub, sup), index).is_some() {
            return Err("live CB positive cells contain a duplicate coordinate".to_string());
        }
    }

    let mut unsatisfiable_index = std::collections::HashMap::new();
    for (index, row) in unsatisfiable.iter().enumerate() {
        let sub = row
            .get("sub")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live CB unsatisfiable row has no numeric subject".to_string())?;
        if unsatisfiable_index.insert(sub, index).is_some() {
            return Err("live CB unsatisfiable rows contain a duplicate subject".to_string());
        }
    }

    let mut published = Vec::with_capacity(named.len().saturating_mul(named.len()));
    let mut cells = Vec::with_capacity(named.len().saturating_mul(named.len()));
    let mut unresolved = 0usize;
    for &sub in &named {
        for &sup in &named {
            let (answer, evidence) = if sub == sup {
                (true, serde_json::json!("reflexive"))
            } else if let Some(&index) = unsatisfiable_index.get(&sub) {
                (
                    true,
                    serde_json::json!({"unsatisfiable": {"live_index": index}}),
                )
            } else if let Some(&index) = positive_index.get(&(sub, sup)) {
                (
                    true,
                    serde_json::json!({"positive": {"live_index": index}}),
                )
            } else if let Some(model) = cb_one_element_countermodel(live_state, sub, sup)? {
                (
                    false,
                    serde_json::json!({"negative": {"witness": 0, "model": model}}),
                )
            } else if let Some(model) = cb_finite_countermodel(live_state, sub, sup, 2)? {
                (
                    false,
                    serde_json::json!({"negative": {"witness": 0, "model": model}}),
                )
            } else if let Some(countermodel) =
                cb_blocked_taxonomy_countermodel(live_publication, sub, sup)?
            {
                (false, serde_json::json!({"blocked": countermodel}))
            } else if let Some(countermodel) = regular_countermodel(sub, sup)?
            {
                (
                    false,
                    serde_json::json!({"regularArbitraryChain": countermodel}),
                )
            } else {
                unresolved += 1;
                (false, serde_json::json!("unresolved"))
            };
            published.push(answer);
            cells.push(serde_json::json!({
                "sub": sub,
                "sup": sup,
                "answer": answer,
                "evidence": evidence,
            }));
        }
    }

    Ok((
        serde_json::json!({
            "version": 1,
            "live": live_publication,
            "named_concepts": named,
            "published": published,
            "cells": cells,
        }),
        unresolved,
    ))
}

fn cb_live_terminal_event_for_clause(
    live_publication: &serde_json::Value,
    context_index: usize,
    clause: &serde_json::Value,
) -> Result<usize, String> {
    let live = live_publication
        .pointer("/derivation/production_bound/live_state")
        .ok_or_else(|| "live CB publication has no live state".to_string())?;
    let context = live
        .get("contexts")
        .and_then(serde_json::Value::as_array)
        .and_then(|contexts| contexts.get(context_index))
        .ok_or_else(|| "CB publication witness references a missing context".to_string())?;
    let root = context
        .get("root")
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| "CB publication context has no arena domain".to_string())?;
    let arena = live
        .get(if root {
            "root_clause_arena"
        } else {
            "ordinary_clause_arena"
        })
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "CB publication live state has no clause arena".to_string())?;
    let retained = context
        .get("retained_clause_ids")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "CB publication context has no retained clauses".to_string())?;
    let clause_id = retained
        .iter()
        .filter_map(serde_json::Value::as_u64)
        .filter_map(|value| usize::try_from(value).ok())
        .find(|&id| arena.get(id) == Some(clause))
        .ok_or_else(|| "CB publication witness has no exact retained clause".to_string())?;
    let history = live
        .get("insertion_history")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "CB publication live state has no insertion history".to_string())?;
    history
        .iter()
        .enumerate()
        .rev()
        .find(|(_, event)| {
            event.get("context_index").and_then(serde_json::Value::as_u64)
                == Some(context_index as u64)
                && event.get("root").and_then(serde_json::Value::as_bool) == Some(root)
                && event.get("clause_id").and_then(serde_json::Value::as_u64)
                    == Some(clause_id as u64)
        })
        .map(|(index, _)| index)
        .ok_or_else(|| "retained CB publication clause has no insertion event".to_string())
}

/// Build a source-bound exact taxonomy that can be checked without trusting
/// the much larger abstract global-closure document. Every positive cell gets
/// a standalone production derivation; every negative cell gets an explicit
/// finite or regular model. This is the extensional soundness-and-completeness
/// boundary for the actual matrix emitted by KM.
fn cb_source_exact_taxonomy_candidate(
    live_publication: &serde_json::Value,
) -> Result<(serde_json::Value, usize), String> {
    let global = live_publication
        .pointer("/derivation/production_bound/global_model")
        .ok_or_else(|| "live CB publication has no typed source certificate".to_string())?;
    let source = cb_regular_arbitrary_chain_source(global)?;
    let (live_exact, _) = cb_exact_taxonomy_candidate(live_publication)?;
    let named = live_exact
        .get("named_concepts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| "live exact CB candidate has no named concepts".to_string())?;
    let names = live_publication
        .pointer("/derivation/production_bound/live_state/concept_names")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| "live CB state has no concept-name table".to_string())?;
    if names.len() != source.concept_count {
        return Err("CB typed source and live concept-name bounds differ".to_string());
    }

    let concept_literal = |concept: usize| {
        serde_json::json!({"predicate": {"predicate": {"concept": {
            "concept": concept, "term": {"var": {"index": 0}}
        }}}})
    };
    let unit_clause = |concept: usize| {
        serde_json::json!({"body": [], "head": [concept_literal(concept)]})
    };
    let live_unit_clause = |concept: usize| {
        serde_json::json!({"body": [], "head": [{
            "kind": "concept", "iri": concept,
            "first": crate::calc::X, "second": null
        }]})
    };
    let empty_clause = serde_json::json!({"body": [], "head": []});
    let positives = live_publication
        .get("public_subsumptions")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no positive cells".to_string())?;
    let unsatisfiable = live_publication
        .get("unsatisfiable")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no unsatisfiable rows".to_string())?;

    let mut cells = Vec::new();
    let mut published = Vec::new();
    let mut public_subsumptions = Vec::new();
    let mut unresolved = 0usize;
    let exact_cells = live_exact
        .get("cells")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live exact CB candidate has no cells".to_string())?;
    for cell in exact_cells {
        let sub = cell
            .get("sub")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live exact CB cell has no subclass".to_string())?;
        let sup = cell
            .get("sup")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live exact CB cell has no superclass".to_string())?;
        let answer = cell
            .get("answer")
            .and_then(serde_json::Value::as_bool)
            .ok_or_else(|| "live exact CB cell has no answer".to_string())?;
        let live_evidence = cell
            .get("evidence")
            .ok_or_else(|| "live exact CB cell has no evidence".to_string())?;
        let evidence = if live_evidence == "reflexive" {
            serde_json::json!({"positiveProduction": {"trace": [{
                "clause": unit_clause(sup),
                "justification": {"assumption": {"index": 0}}
            }]}})
        } else if let Some(index) = live_evidence
            .pointer("/positive/live_index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
        {
            let context_index = positives
                .get(index)
                .and_then(|positive| positive.get("context_index"))
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| "positive CB witness has no context index".to_string())?;
            let event = cb_live_terminal_event_for_clause(
                live_publication,
                context_index,
                &live_unit_clause(sup),
            )?;
            let trace = cb_standalone_production_trace(live_publication, event)?;
            serde_json::json!({"positiveProduction": {"trace": trace}})
        } else if let Some(index) = live_evidence
            .pointer("/unsatisfiable/live_index")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
        {
            let context_index = unsatisfiable
                .get(index)
                .and_then(|row| row.get("context_index"))
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| "unsatisfiable CB witness has no context index".to_string())?;
            let event = cb_live_terminal_event_for_clause(
                live_publication,
                context_index,
                &empty_clause,
            )?;
            let trace = cb_standalone_production_trace(live_publication, event)?;
            serde_json::json!({"positiveProduction": {"trace": trace}})
        } else if let Some(negative) = live_evidence.get("negative") {
            serde_json::json!({"negative": negative})
        } else if let Some(regular) = live_evidence.get("regularArbitraryChain") {
            serde_json::json!({"regularArbitraryChain": {"model": regular}})
        } else if !answer {
            match cb_regular_arbitrary_chain_countermodel(&source, sub, sup)? {
                Some(regular) => {
                    serde_json::json!({"regularArbitraryChain": {"model": regular}})
                }
                None => {
                    unresolved += 1;
                    serde_json::json!({"negative": {
                        "witness": 0,
                        "model": {"domain_size": 0, "concepts": [], "roles": [],
                            "constants": [], "functions": []}
                    }})
                }
            }
        } else {
            return Err("true CB cell has no positive derivation".to_string());
        };
        if answer && sub != sup {
            let sub_name = names
                .get(sub)
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "CB subclass has no public name".to_string())?;
            let sup_name = names
                .get(sup)
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| "CB superclass has no public name".to_string())?;
            public_subsumptions.push(serde_json::json!({"sub": sub_name, "sup": sup_name}));
        }
        published.push(answer);
        cells.push(serde_json::json!({
            "core_concept": sub,
            "superconcept": sup,
            "answer": answer,
            "evidence": evidence,
        }));
    }

    let taxonomy = serde_json::json!({
        "version": 2,
        "concept_count": source.concept_count,
        "role_count": source.role_count,
        "function_count": source.function_count,
        "individual_count": source.individual_count,
        "ontology": source.source_ontology,
        "concept_names": names,
        "named_concepts": named,
        "published": published,
        "public_subsumptions": public_subsumptions,
        "cells": cells,
    });
    Ok((serde_json::json!({
        "version": 1,
        "source": source.source_binding,
        "taxonomy": taxonomy,
    }), unresolved))
}

fn cb_source_production_taxonomy_candidate(
    live_publication: &serde_json::Value,
) -> Result<(serde_json::Value, usize), String> {
    let (legacy, unresolved) = cb_source_exact_taxonomy_candidate(live_publication)?;
    let taxonomy = legacy
        .get("taxonomy")
        .ok_or_else(|| "source-exact CB candidate has no taxonomy".to_string())?;
    let named = taxonomy
        .get("named_concepts")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| "source-exact CB taxonomy has no named concepts".to_string())?;
    let events = cb_public_witness_events(live_publication)?;
    let (mut proof_document, event_nodes) =
        cb_standalone_context_proof_document(live_publication, &events)?;
    let proof_nodes = proof_document
        .pointer_mut("/proof/nodes")
        .and_then(serde_json::Value::as_array_mut)
        .ok_or_else(|| "standalone CB proof has no node array".to_string())?;
    let concept_predicate = |concept: usize| {
        serde_json::json!({"concept": {
            "concept": concept, "term": {"var": {"index": 0}}
        }})
    };
    let concept_literal = |concept: usize| {
        serde_json::json!({"predicate": {"predicate": concept_predicate(concept)}})
    };
    let unit = |concept: usize| {
        serde_json::json!({"body": [], "head": [concept_literal(concept)]})
    };
    let mut reflexive_nodes = std::collections::HashMap::new();
    for value in &named {
        let concept = value
            .as_u64()
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "named CB concept is not numeric".to_string())?;
        let node = proof_nodes.len();
        proof_nodes.push(serde_json::json!({
            "core": [concept_predicate(concept)],
            "clause": unit(concept),
            "evidence": {"local": {
                "prior_nodes": [],
                "trace": [{
                    "clause": unit(concept),
                    "justification": {"assumption": {"index": 0}},
                }],
            }},
        }));
        reflexive_nodes.insert(concept, node);
    }

    let live_exact = cb_exact_taxonomy_candidate(live_publication)?.0;
    let live_cells = live_exact
        .get("cells")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live exact CB candidate has no cells".to_string())?;
    let legacy_cells = taxonomy
        .get("cells")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "source-exact CB taxonomy has no cells".to_string())?;
    if live_cells.len() != legacy_cells.len() {
        return Err("live and source-exact CB matrix lengths differ".to_string());
    }
    let positives = live_publication
        .get("public_subsumptions")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no positive cells".to_string())?;
    let unsatisfiable = live_publication
        .get("unsatisfiable")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "live CB publication has no unsatisfiable rows".to_string())?;
    let live_unit = |concept: usize| {
        serde_json::json!({"body": [], "head": [{
            "kind": "concept", "iri": concept,
            "first": crate::calc::X, "second": null
        }]})
    };
    let empty = serde_json::json!({"body": [], "head": []});
    let mut cells = Vec::with_capacity(legacy_cells.len());
    for (live_cell, legacy_cell) in live_cells.iter().zip(legacy_cells) {
        let sub = live_cell
            .get("sub")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live CB cell has no subclass".to_string())?;
        let sup = live_cell
            .get("sup")
            .and_then(serde_json::Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| "live CB cell has no superclass".to_string())?;
        let answer = live_cell
            .get("answer")
            .and_then(serde_json::Value::as_bool)
            .ok_or_else(|| "live CB cell has no answer".to_string())?;
        let evidence = if answer {
            let node = if sub == sup {
                *reflexive_nodes
                    .get(&sub)
                    .ok_or_else(|| "reflexive CB cell has no proof node".to_string())?
            } else if let Some(index) = live_cell
                .pointer("/evidence/positive/live_index")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
            {
                let positive = positives
                    .get(index)
                    .ok_or_else(|| "positive CB cell index is out of bounds".to_string())?;
                let context = positive
                    .get("context_index")
                    .and_then(serde_json::Value::as_u64)
                    .and_then(|value| usize::try_from(value).ok())
                    .ok_or_else(|| "positive CB cell has no context".to_string())?;
                let event = cb_live_terminal_event_for_clause(
                    live_publication,
                    context,
                    &live_unit(sup),
                )?;
                *event_nodes
                    .get(&event)
                    .ok_or_else(|| "positive CB witness is absent from the shared DAG".to_string())?
            } else if let Some(index) = live_cell
                .pointer("/evidence/unsatisfiable/live_index")
                .and_then(serde_json::Value::as_u64)
                .and_then(|value| usize::try_from(value).ok())
            {
                let row = unsatisfiable
                    .get(index)
                    .ok_or_else(|| "unsatisfiable CB row index is out of bounds".to_string())?;
                let context = row
                    .get("context_index")
                    .and_then(serde_json::Value::as_u64)
                    .and_then(|value| usize::try_from(value).ok())
                    .ok_or_else(|| "unsatisfiable CB row has no context".to_string())?;
                let event = cb_live_terminal_event_for_clause(live_publication, context, &empty)?;
                *event_nodes.get(&event).ok_or_else(||
                    "unsatisfiable CB witness is absent from the shared DAG".to_string())?
            } else {
                return Err("true CB cell has no shared production witness".to_string());
            };
            serde_json::json!({"positiveNode": {"node": node}})
        } else {
            let legacy_evidence = legacy_cell
                .get("evidence")
                .cloned()
                .ok_or_else(|| "negative CB cell has no evidence".to_string())?;
            if let Some(regular) = legacy_evidence.get("regularArbitraryChain") {
                serde_json::json!({"typedRegularArbitraryChain": regular})
            } else {
                legacy_evidence
            }
        };
        cells.push(serde_json::json!({
            "sub": sub,
            "sup": sup,
            "answer": answer,
            "evidence": evidence,
        }));
    }
    Ok((serde_json::json!({
        "version": 1,
        "source": legacy.get("source").cloned().ok_or_else(||
            "source-exact CB candidate has no source".to_string())?,
        "proof": proof_document.get("proof").cloned().ok_or_else(||
            "standalone CB document has no proof".to_string())?,
        "concept_names": taxonomy.get("concept_names").cloned().ok_or_else(||
            "source-exact CB taxonomy has no concept names".to_string())?,
        "named_concepts": named,
        "published": taxonomy.get("published").cloned().ok_or_else(||
            "source-exact CB taxonomy has no publication bits".to_string())?,
        "public_subsumptions": taxonomy.get("public_subsumptions").cloned().ok_or_else(||
            "source-exact CB taxonomy has no public payload".to_string())?,
        "cells": cells,
    }), unresolved))
}

/// Translate the exact grouped answer into the semantic ids and live-context
/// witnesses checked by Lean. Any row without a direct retained witness makes
/// certified publication fail closed.
fn cb_live_publication_rows(
    live: &crate::engine::CbLiveTerminalSnapshot,
    answer: &std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
) -> Result<
    (
        Vec<serde_json::Value>,
        Vec<serde_json::Value>,
        Vec<serde_json::Value>,
    ),
    String,
> {
    let ids: std::collections::HashMap<&str, usize> = live
        .concept_names
        .iter()
        .enumerate()
        .map(|(id, name)| (name.as_str(), id))
        .collect();
    if ids.len() != live.concept_names.len() {
        return Err("CB concept-name interner contains duplicate public names".to_string());
    }
    let mut rows = Vec::with_capacity(answer.len());
    let mut cells = Vec::new();
    let mut unsatisfiable = Vec::new();
    for (sub_name, supers) in answer {
        let sub = *ids
            .get(sub_name.as_str())
            .ok_or_else(|| format!("published CB subject {sub_name:?} is not interned"))?;
        let (context_index, context) = live
            .contexts
            .iter()
            .enumerate()
            .find(|(_, context)| context.query_concept == Some(sub as crate::calc::Iri))
            .ok_or_else(|| format!("published CB subject {sub_name:?} has no query context"))?;
        let arena = if context.root {
            &live.root_clause_arena
        } else {
            &live.ordinary_clause_arena
        };
        let retained: Vec<&crate::engine::CbLiveClause> = context
            .retained_clause_ids
            .iter()
            .map(|&id| {
                arena
                    .get(id as usize)
                    .ok_or_else(|| format!("context {context_index} retains missing clause {id}"))
            })
            .collect::<Result<_, _>>()?;
        let contradiction = retained
            .iter()
            .any(|clause| clause.body.is_empty() && clause.head.is_empty());
        let mut numeric_supers = Vec::new();
        let mut row_unsatisfiable = false;
        for sup_name in supers {
            if sup_name == "owl:Nothing" {
                if !contradiction {
                    return Err(format!(
                        "published CB unsatisfiable subject {sub_name:?} has no retained contradiction"
                    ));
                }
                row_unsatisfiable = true;
                unsatisfiable.push(serde_json::json!({
                    "sub": sub,
                    "context_index": context_index,
                }));
                continue;
            }
            let sup = *ids
                .get(sup_name.as_str())
                .ok_or_else(|| format!("published CB superclass {sup_name:?} is not interned"))?;
            let witnessed = retained.iter().any(|clause| {
                clause.body.is_empty()
                    && clause.head.len() == 1
                    && clause.head[0].kind == "concept"
                    && clause.head[0].iri == Some(sup as crate::calc::Iri)
                    && clause.head[0].first == crate::calc::X
                    && clause.head[0].second.is_none()
            });
            if !witnessed {
                return Err(format!(
                    "published CB cell {sub_name:?} <= {sup_name:?} has no retained unit witness"
                ));
            }
            numeric_supers.push(sup);
            cells.push(serde_json::json!({
                "sub": sub,
                "sup": sup,
                "context_index": context_index,
            }));
        }
        rows.push(serde_json::json!({
            "sub": sub,
            "supers": numeric_supers,
            "unsatisfiable": row_unsatisfiable,
        }));
    }
    Ok((rows, cells, unsatisfiable))
}

/// Find the source-bound production context array already present in the
/// nested global certificate. A shape match alone is insufficient because the
/// document contains several nested context arrays. Require the exact live
/// context count and context ids; Lean still independently decodes and binds
/// every copied trace.
fn find_cb_production_contexts<'a>(
    value: &'a serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
) -> Option<&'a Vec<serde_json::Value>> {
    if let Some(object) = value.as_object() {
        if object.contains_key("source") && object.contains_key("individual_count") {
            if let Some(contexts) = object.get("contexts").and_then(serde_json::Value::as_array) {
                let exact = contexts.len() == live.contexts.len()
                    && contexts
                        .iter()
                        .zip(&live.contexts)
                        .all(|(candidate, context)| {
                            candidate
                                .get("context_id")
                                .and_then(serde_json::Value::as_u64)
                            == Some(context.context_id as u64)
                                && candidate
                                    .get("trace")
                                    .is_some_and(serde_json::Value::is_array)
                    });
                if exact {
                    return Some(contexts);
                }
            }
        }
        for child in object.values() {
            if let Some(found) = find_cb_production_contexts(child, live) {
                return Some(found);
            }
        }
    } else if let Some(array) = value.as_array() {
        for child in array {
            if let Some(found) = find_cb_production_contexts(child, live) {
                return Some(found);
            }
        }
    }
    None
}

/// Locate the exact Pred send-coverage branch inside a nested production
/// certificate. The terminal-state emitter copies this checked branch and
/// supplies only operational fields read from the same live engine snapshot.
fn find_cb_pred_send_coverage(value: &serde_json::Value) -> Option<&serde_json::Value> {
    if let Some(object) = value.as_object() {
        let is_send_coverage = object.get("version").and_then(serde_json::Value::as_u64)
            == Some(2)
            && object.contains_key("inter_context")
            && object.contains_key("ground_context_index")
            && object.get("senders").is_some_and(serde_json::Value::is_array)
            && object.contains_key("root_sender");
        if is_send_coverage {
            return Some(value);
        }
        for child in object.values() {
            if let Some(found) = find_cb_pred_send_coverage(child) {
                return Some(found);
            }
        }
    } else if let Some(array) = value.as_array() {
        for child in array {
            if let Some(found) = find_cb_pred_send_coverage(child) {
                return Some(found);
            }
        }
    }
    None
}

fn cb_wire_predicate(predicate: &crate::engine::CbLivePred, bits: u32) -> serde_json::Value {
    cb_wire_literal(&cb_live_pred_literal(predicate), bits)["predicate"]["predicate"].clone()
}

/// Construct the soundness certificate directly from the in-band typed source
/// and the live terminal snapshot. Every final retained clause is an explicit
/// local import and is replayed by an assumption entry. This local trace alone
/// is intentionally conditional; the independently checked chronological
/// insertion DAG discharges every import and prevents circular trust.
fn cb_source_live_derivation_candidate(
    source: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
    insertion_evidence: &[serde_json::Value],
) -> Result<serde_json::Value, String> {
    let live_json = serde_json::to_value(live)
        .map_err(|error| format!("cannot serialize live CB snapshot: {error}"))?;
    let mut contexts = Vec::with_capacity(live.contexts.len());
    for context in &live.contexts {
        let arena = if context.root {
            &live.root_clause_arena
        } else {
            &live.ordinary_clause_arena
        };
        let retained = context
            .retained_clause_ids
            .iter()
            .map(|clause_id| {
                arena
                    .get(*clause_id as usize)
                    .map(|clause| cb_wire_clause(clause, live.comp_ind_bits))
                    .ok_or_else(|| {
                        format!(
                            "CB context {} retains missing clause {clause_id}",
                            context.context_index
                        )
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let core = context
            .core
            .iter()
            .map(|predicate| cb_wire_predicate(predicate, live.comp_ind_bits))
            .collect::<Vec<_>>();
        let trace = retained
            .iter()
            .enumerate()
            .map(|(index, clause)| {
                serde_json::json!({
                    "clause": clause,
                    "justification": {"assumption": {
                        "index": core.len() + index
                    }}
                })
            })
            .collect::<Vec<_>>();
        contexts.push(serde_json::json!({
            "context_id": context.context_id,
            "root": context.root,
            "nominal_ground": context.nominal_ground,
            "query_concept": context.query_concept,
            "core": core,
            "imports": retained,
            "retained": retained,
            "discarded": [],
            "trace": trace,
        }));
    }
    let production = serde_json::json!({
        "version": 2,
        "source": source,
        "individual_count": live.runtime_individual_count,
        "contexts": contexts,
    });
    Ok(serde_json::json!({
        "version": 1,
        "production": production,
        "comp_ind_bits": live.comp_ind_bits,
        "ordinary_clause_arena": live_json.get("ordinary_clause_arena")
            .cloned().ok_or_else(|| "live CB snapshot omits ordinary arena".to_string())?,
        "root_clause_arena": live_json.get("root_clause_arena")
            .cloned().ok_or_else(|| "live CB snapshot omits root arena".to_string())?,
        "insertion_history": live_json.get("insertion_history")
            .cloned().ok_or_else(|| "live CB snapshot omits insertion history".to_string())?,
        "contexts": live_json.get("contexts")
            .cloned().ok_or_else(|| "live CB snapshot omits contexts".to_string())?,
        "insertion_evidence": insertion_evidence,
        "pending_messages": live.pending_messages,
        "message_truncated": live.message_truncated,
        "nominal_truncated": live.nominal_truncated,
    }))
}

fn cb_source_finite_order_candidate(
    live: &crate::engine::CbLiveTerminalSnapshot,
) -> Result<serde_json::Value, String> {
    use crate::calc::{COMP_BASE, FTERM_BASE, X};

    let mut raw_terms = Vec::new();
    let mut note_term = |term: crate::calc::Term| {
        if !raw_terms.contains(&term) {
            raw_terms.push(term);
        }
        if (FTERM_BASE..COMP_BASE).contains(&term) && !raw_terms.contains(&X) {
            raw_terms.push(X);
        }
    };
    let mut literals = Vec::new();
    let mut note_clause = |clause: &crate::engine::CbLiveClause| {
        for literal in clause.body.iter().chain(&clause.head) {
            note_term(literal.first);
            if let Some(second) = literal.second {
                note_term(second);
            }
            let wire = cb_wire_literal(literal, live.comp_ind_bits);
            if wire.is_null() {
                return Err("live CB ordering contains an unsupported literal".to_string());
            }
            cb_push_unique(&mut literals, wire);
        }
        Ok(())
    };
    for clause in &live.source_ontology {
        note_clause(clause)?;
    }
    for context in &live.contexts {
        let arena = if context.root {
            &live.root_clause_arena
        } else {
            &live.ordinary_clause_arena
        };
        for &clause_id in &context.retained_clause_ids {
            let clause = arena.get(clause_id as usize).ok_or_else(|| {
                format!("CB ordering context retains missing clause {clause_id}")
            })?;
            note_clause(clause)?;
        }
    }
    raw_terms.sort_unstable();
    let mut ordered_terms = raw_terms
        .iter().copied().filter(|term| *term <= X)
        .map(|term| cb_wire_term(term, live.comp_ind_bits))
        .collect::<Vec<_>>();
    ordered_terms.extend(raw_terms.iter().copied()
        .filter(|term| (*term > X) && (*term < FTERM_BASE))
        .map(|term| cb_wire_term(term, live.comp_ind_bits)));
    ordered_terms.extend(raw_terms.iter().copied()
        .filter(|term| (FTERM_BASE..COMP_BASE).contains(term))
        .map(|term| cb_wire_term(term, live.comp_ind_bits)));
    ordered_terms.extend(raw_terms.iter().copied()
        .filter(|term| *term >= COMP_BASE)
        .map(|term| cb_wire_term(term, live.comp_ind_bits)));
    ordered_terms.dedup();

    let pred_triggers = live.pred_trigger_literals.iter()
        .map(|literal| cb_wire_literal(literal, live.comp_ind_bits))
        .collect::<Vec<_>>();
    if pred_triggers.iter().any(serde_json::Value::is_null) {
        return Err("live CB predecessor trigger is unsupported".to_string());
    }
    Ok(serde_json::json!({
        "ordered_terms": ordered_terms,
        "ordered_literals": literals,
        "root_concept_mode": live.root_concept_order_mode,
        "non_root_concept_mode": live.non_root_concept_order_mode,
        "internal_concepts": live.concept_internal,
        "pred_triggers": pred_triggers,
    }))
}

fn cb_source_hyper_closure_candidate(
    source: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
    insertion_evidence: &[serde_json::Value],
) -> Result<serde_json::Value, String> {
    let live_candidate = cb_source_live_derivation_candidate(source, live, insertion_evidence)?;
    Ok(serde_json::json!({
        "version": 1,
        "local_closure": {"version": 1, "live": live_candidate},
        "order": cb_source_finite_order_candidate(live)?,
    }))
}

fn cb_source_succ_closure_candidate(
    source: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
    insertion_evidence: &[serde_json::Value],
) -> Result<serde_json::Value, String> {
    let hyper = cb_source_hyper_closure_candidate(source, live, insertion_evidence)?;
    Ok(serde_json::json!({
        "version": 1,
        "join3_closure": {"version": 1, "hyper_closure": hyper},
        "rsucc_enabled": live.rsucc_enabled,
        "reach_concepts": live.reach_concept_ids,
    }))
}

fn cb_source_eq_closure_candidate(
    source: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
    insertion_evidence: &[serde_json::Value],
) -> Result<serde_json::Value, String> {
    let succ = cb_source_succ_closure_candidate(source, live, insertion_evidence)?;
    Ok(serde_json::json!({"version": 1, "succ_closure": succ}))
}

fn cb_source_root_pred_closure_candidate(
    source: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
    insertion_evidence: &[serde_json::Value],
) -> Result<serde_json::Value, String> {
    let eq = cb_source_eq_closure_candidate(source, live, insertion_evidence)?;
    Ok(serde_json::json!({
        "version": 1,
        "ordinary_pred_closure": {"version": 1, "eq_closure": eq}
    }))
}

/// Reconstruct the exact Pred send partition from the terminal engine state.
/// `pred_pool_seen` is the production record of every pool clause actually
/// sent over an edge. Historical IDs removed by back-subsumption are omitted,
/// because the independent Lean enumerators range over the final retained
/// snapshot. Sorting the remaining records clause-major/edge-minor reproduces
/// those enumerators; the checker rejects any omitted or ineligible send. Only
/// the checked production trace and optional Nom allocation are copied from
/// the enclosing document.
fn cb_pred_send_coverage_candidate(
    global_model: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
) -> Result<serde_json::Value, String> {
    let prior = find_cb_pred_send_coverage(global_model)
        .ok_or_else(|| "CB global certificate has no Pred send-coverage branch".to_string())?;
    let production = prior
        .pointer("/inter_context/production")
        .cloned()
        .ok_or_else(|| "CB Pred send-coverage branch has no production trace".to_string())?;
    let ground = live
        .contexts
        .iter()
        .find(|context| context.nominal_ground)
        .map(|context| context.context_index);
    if live.contexts.iter().filter(|context| context.nominal_ground).count() > 1 {
        return Err("CB live state has multiple nominal-ground contexts".to_string());
    }

    let mut transfers = Vec::new();
    let mut ordinary_senders = Vec::new();
    let mut root_sender = None;
    for sender in &live.contexts {
        let mut edges = Vec::new();
        for receiver in &live.contexts {
            for edge in &receiver.predecessors {
                if edge.predecessor_context == sender.context_index {
                    edges.push((receiver, edge));
                }
            }
        }
        let arena = if sender.root {
            &live.root_clause_arena
        } else {
            &live.ordinary_clause_arena
        };
        let mut sends = Vec::new();
        for (edge_index, (_, edge)) in edges.iter().enumerate() {
            for clause_id in &edge.pred_pool_seen {
                let Some(retained_index) = sender
                    .retained_clause_ids
                    .iter()
                    .position(|retained| retained == clause_id)
                else {
                    continue;
                };
                sends.push((retained_index, edge_index, *clause_id));
            }
        }
        sends.sort_unstable();
        sends.dedup();
        let mut transfer_indices = Vec::with_capacity(sends.len());
        for (retained_index, edge_index, clause_id) in sends {
            let (receiver, edge) = edges[edge_index];
            let clause = arena.get(clause_id as usize).ok_or_else(|| {
                format!(
                    "CB Pred sender {} references missing clause {clause_id}",
                    sender.context_index
                )
            })?;
            let map = |term| cb_pred_backwards(term, edge.label, live.comp_ind_bits);
            let mut payload = crate::engine::CbLiveClause {
                body: clause
                    .body
                    .iter()
                    .map(|literal| cb_map_live_literal(literal, map))
                    .collect(),
                head: clause
                    .head
                    .iter()
                    .map(|literal| cb_map_live_literal(literal, map))
                    .collect(),
            };
            for predicate in &sender.core {
                cb_push_unique(
                    &mut payload.body,
                    cb_map_live_literal(&cb_live_pred_literal(predicate), map),
                );
            }
            let transfer_index = transfers.len();
            transfer_indices.push(transfer_index);
            transfers.push(serde_json::json!({
                "sender_context_index": sender.context_index,
                "sender_context_id": sender.context_id,
                "receiver_context_index": receiver.context_index,
                "receiver_context_id": receiver.context_id,
                "retained_clause_index": retained_index,
                "substitution": [
                    {"variableId": -1, "term": {"var": {"index": 0}}},
                    {"variableId": 0, "term": cb_wire_term(edge.label, live.comp_ind_bits)},
                ],
                "payload": cb_wire_clause(&payload, live.comp_ind_bits),
            }));
        }
        let wire_edges = edges
            .iter()
            .map(|(receiver, edge)| {
                serde_json::json!({
                    "receiver_context_index": receiver.context_index,
                    "receiver_context_id": receiver.context_id,
                    "label": cb_wire_term(edge.label, live.comp_ind_bits),
                    "pushed": edge.pushed.iter().map(|predicate|
                        cb_wire_predicate(predicate, live.comp_ind_bits)).collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>();
        let snapshot = serde_json::json!({
            "sender_context_index": sender.context_index,
            "sender_context_id": sender.context_id,
            "edges": wire_edges,
            "transfer_indices": transfer_indices,
        });
        if Some(sender.context_index) == ground {
            root_sender = Some(snapshot);
        } else {
            ordinary_senders.push(snapshot);
        }
    }

    Ok(serde_json::json!({
        "version": 2,
        "inter_context": {
            "version": 1,
            "production": production,
            "transfers": transfers,
            "arrivals": [],
        },
        "ground_context_index": ground,
        "senders": ordinary_senders,
        "root_sender": root_sender,
        "nominal_allocation": prior.get("nominal_allocation").cloned()
            .unwrap_or(serde_json::Value::Null),
    }))
}

/// Serialize the operational CB terminal document consumed by
/// `CBTerminalStateWire`. In particular, `edge_seen` comes from each receiver
/// context's predecessor map, while successor-pair reach watermarks come from
/// that context's outgoing successor records. Lean independently relates both
/// lists to the copied send-coverage branch.
fn cb_terminal_state_candidate(
    global_model: &serde_json::Value,
    live: &crate::engine::CbLiveTerminalSnapshot,
) -> Result<serde_json::Value, String> {
    let send_coverage = cb_pred_send_coverage_candidate(global_model, live)?;
    let contexts = live
        .contexts
        .iter()
        .map(|context| {
            serde_json::json!({
                "context_index": context.context_index,
                "context_id": context.context_id,
                "todo_count": context.todo_clause_ids.len(),
                "dirty": context.dirty,
                "pred_pool_len": context.pred_pool_ids.len(),
                "pred_hwm": context.pred_hwm,
                "succ_pool_len": context.succ_pool_ids.len(),
                "succ_hwm": context.succ_hwm,
                "rsucc_pool_len": context.rsucc_pool_ids.len(),
                "rsucc_hwm": context.rsucc_hwm,
                "rsucc_reach_len": context.rsucc_reach.len(),
                "rsucc_offered": context.rsucc_offered,
                "rsucc_pair_reach_hwm": context.successor_reach_hwm,
                "rsucc_edges_grew": context.rsucc_edges_grew,
                "edge_seen": context.predecessor_edge_seen,
            })
        })
        .collect::<Vec<_>>();
    Ok(serde_json::json!({
        "version": 1,
        "send_coverage": send_coverage,
        "pending_messages": live.pending_messages,
        "message_truncated": live.message_truncated,
        "nominal_truncated": live.nominal_truncated,
        "contexts": contexts,
    }))
}

#[cfg(test)]
mod cb_derivation_candidate_tests {
    use super::*;

    fn live_context(
        context_index: usize,
        context_id: usize,
    ) -> crate::engine::CbLiveContextSnapshot {
        crate::engine::CbLiveContextSnapshot {
            context_index,
            context_id,
            root: true,
            nominal_ground: false,
            query_concept: None,
            core: Vec::new(),
            retained_clause_ids: Vec::new(),
            todo_clause_ids: Vec::new(),
            dirty: false,
            pred_pool_ids: Vec::new(),
            pred_hwm: 0,
            succ_pool_ids: Vec::new(),
            succ_hwm: 0,
            rsucc_pool_ids: Vec::new(),
            rsucc_hwm: 0,
            rsucc_reach: Vec::new(),
            rsucc_offered: 0,
            rsucc_edges_grew: false,
            predecessors: Vec::new(),
            successors: Vec::new(),
            predecessor_edge_seen: Vec::new(),
            successor_reach_hwm: Vec::new(),
        }
    }

    fn live_snapshot() -> crate::engine::CbLiveTerminalSnapshot {
        crate::engine::CbLiveTerminalSnapshot {
            version: 6,
            comp_ind_bits: 17,
            concept_count: 1,
            concept_names: vec!["A".to_string()],
            concept_internal: vec![false],
            forward_role_succ_trigger: Vec::new(),
            backward_role_succ_trigger: Vec::new(),
            root_concept_order_mode: "incomparable".to_string(),
            non_root_concept_order_mode: "incomparable".to_string(),
            pred_trigger_literals: Vec::new(),
            role_count: 0,
            function_count: 1,
            source_individual_count: 0,
            runtime_individual_count: 0,
            source_ontology: Vec::new(),
            rsucc_enabled: false,
            reach_concept_ids: Vec::new(),
            ordinary_clause_arena: Vec::new(),
            root_clause_arena: Vec::new(),
            pending_messages: 0,
            message_truncated: false,
            nominal_truncated: false,
            insertion_history: Vec::new(),
            contexts: vec![live_context(0, 7), live_context(1, 11)],
        }
    }

    fn accepted_pred_production() -> serde_json::Value {
        let x = serde_json::json!({"var": {"index": 0}});
        let a = serde_json::json!({"predicate": {"predicate": {"concept": {
            "concept": 0, "term": x.clone()
        }}}});
        let b = serde_json::json!({"predicate": {"predicate": {"concept": {
            "concept": 1, "term": x.clone()
        }}}});
        let clause = serde_json::json!({"body": [a.clone()], "head": [b.clone()]});
        serde_json::json!({
            "version": 2,
            "source": {
                "version": 1,
                "concept_count": 2,
                "role_count": 0,
                "function_count": 1,
                "individual_count": 0,
                "source_clauses": [{"gci": {"body": [0], "head": [1]}}],
                "role_chains": [],
                "role_axioms": [],
                "ontology": [clause.clone()],
                "function_allocation": null
            },
            "individual_count": 0,
            "contexts": [{
                "context_id": 7,
                "root": false,
                "nominal_ground": false,
                "query_concept": null,
                "core": [{"concept": {"concept": 0, "term": x}}],
                "retained": [clause.clone()],
                "discarded": [],
                "trace": [{
                    "clause": clause,
                    "justification": {"premise": {"index": 0, "substitution": []}}
                }]
            }]
        })
    }

    #[test]
    fn production_trace_extraction_requires_exact_live_context_identity() {
        let document = serde_json::json!({
            "decoy": {
                "source": {}, "individual_count": 0,
                "contexts": [{"context_id": 7, "trace": ["wrong"]}]
            },
            "nested": {
                "source": {}, "individual_count": 0,
                "contexts": [
                    {"context_id": 7, "trace": ["first"]},
                    {"context_id": 11, "trace": ["second"]}
                ]
            }
        });
        let live = live_snapshot();
        let contexts = find_cb_production_contexts(&document, &live).unwrap();
        assert_eq!(contexts[0]["trace"], serde_json::json!(["first"]));
        assert_eq!(contexts[1]["trace"], serde_json::json!(["second"]));

        let forged = serde_json::json!({
            "source": {}, "individual_count": 0,
            "contexts": [
                {"context_id": 7, "trace": []},
                {"context_id": 12, "trace": []}
            ]
        });
        assert!(find_cb_production_contexts(&forged, &live).is_none());
    }

    #[test]
    fn terminal_state_candidate_uses_receiver_and_successor_watermarks() {
        let send_coverage = serde_json::json!({
            "version": 2,
            "inter_context": {"production": {"marker": "production"}},
            "ground_context_index": null,
            "senders": [],
            "root_sender": null,
            "nominal_allocation": null,
        });
        let global = serde_json::json!({"nested": {"send": send_coverage}});
        let mut live = live_snapshot();
        live.pending_messages = 3;
        live.contexts[0].todo_clause_ids = vec![4, 9];
        live.contexts[0].pred_pool_ids = vec![1, 2, 3];
        live.contexts[0].pred_hwm = 2;
        live.contexts[0].predecessor_edge_seen = vec![5, 8];
        live.contexts[0].successor_reach_hwm = vec![13];
        let terminal = cb_terminal_state_candidate(&global, &live).unwrap();
        assert_eq!(
            terminal["send_coverage"]["inter_context"]["production"],
            serde_json::json!({"marker": "production"})
        );
        assert_eq!(terminal["send_coverage"]["inter_context"]["transfers"], serde_json::json!([]));
        assert_eq!(terminal["send_coverage"]["senders"].as_array().unwrap().len(), 2);
        assert_eq!(terminal["send_coverage"]["senders"][0]["sender_context_index"], 0);
        assert_eq!(terminal["send_coverage"]["senders"][1]["sender_context_index"], 1);
        assert_eq!(terminal["pending_messages"], 3);
        assert_eq!(terminal["contexts"][0]["todo_count"], 2);
        assert_eq!(terminal["contexts"][0]["pred_pool_len"], 3);
        assert_eq!(terminal["contexts"][0]["pred_hwm"], 2);
        assert_eq!(
            terminal["contexts"][0]["edge_seen"],
            serde_json::json!([5, 8])
        );
        assert_eq!(
            terminal["contexts"][0]["rsucc_pair_reach_hwm"],
            serde_json::json!([13])
        );
    }

    #[test]
    fn terminal_state_candidate_requires_certified_send_coverage() {
        let error =
            cb_terminal_state_candidate(&serde_json::json!({"version": 1}), &live_snapshot())
                .unwrap_err();
        assert!(error.contains("no Pred send-coverage"));
    }

    #[test]
    fn pred_send_candidate_reconstructs_actual_clause_major_transfer() {
        let x = crate::calc::X;
        let function = crate::calc::FTERM_BASE;
        let a = crate::engine::CbLivePred {
            kind: "concept",
            iri: 0,
            first: x,
            second: None,
        };
        let b = crate::engine::CbLivePred {
            kind: "concept",
            iri: 1,
            first: x,
            second: None,
        };
        let clause = crate::engine::CbLiveClause {
            body: vec![cb_live_pred_literal(&a)],
            head: vec![cb_live_pred_literal(&b)],
        };
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.ordinary_clause_arena = vec![clause];
        live.contexts[0].root = false;
        live.contexts[0].retained_clause_ids = vec![0];
        live.contexts[0].pred_pool_ids = vec![0];
        live.contexts[0].pred_hwm = 1;
        live.contexts[1].predecessors = vec![crate::engine::CbLivePredecessorEdge {
            predecessor_context: 0,
            label: function,
            pushed: vec![a],
            // ID 9 was sent historically and then removed by back-subsumption.
            pred_pool_seen: vec![0, 9],
            edge_seen: 1,
        }];
        live.contexts[1].predecessor_edge_seen = vec![1];
        let global = serde_json::json!({
            "send": {
                "version": 2,
                "inter_context": {"production": {"marker": "production"}},
                "ground_context_index": null,
                "senders": [],
                "root_sender": null,
                "nominal_allocation": null
            }
        });
        let candidate = cb_pred_send_coverage_candidate(&global, &live).unwrap();
        assert_eq!(candidate["senders"][0]["transfer_indices"], serde_json::json!([0]));
        assert_eq!(candidate["senders"][1]["transfer_indices"], serde_json::json!([]));
        assert_eq!(candidate["inter_context"]["transfers"].as_array().unwrap().len(), 1);
        let transfer = &candidate["inter_context"]["transfers"][0];
        assert_eq!(transfer["sender_context_index"], 0);
        assert_eq!(transfer["receiver_context_index"], 1);
        assert_eq!(transfer["retained_clause_index"], 0);
        assert_eq!(transfer["substitution"][1]["term"], cb_wire_term(function, 17));
        assert_eq!(
            transfer["payload"]["head"][0],
            cb_wire_literal(
                &cb_map_live_literal(&cb_live_pred_literal(&b), |term| {
                    cb_pred_backwards(term, function, 17)
                }),
                17
            )
        );
    }

    #[test]
    fn native_pred_send_candidate_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_CB_TEST_PRED_SEND_COVERAGE_CHECKER") else {
            return;
        };
        let x = crate::calc::X;
        let function = crate::calc::FTERM_BASE;
        let a = crate::engine::CbLivePred {
            kind: "concept", iri: 0, first: x, second: None,
        };
        let b = crate::engine::CbLivePred {
            kind: "concept", iri: 1, first: x, second: None,
        };
        let clause = crate::engine::CbLiveClause {
            body: vec![cb_live_pred_literal(&a)],
            head: vec![cb_live_pred_literal(&b)],
        };
        let mut context = live_context(0, 7);
        context.root = false;
        context.core = vec![a.clone()];
        context.retained_clause_ids = vec![0];
        context.pred_pool_ids = vec![0];
        context.pred_hwm = 1;
        context.predecessors = vec![crate::engine::CbLivePredecessorEdge {
            predecessor_context: 0,
            label: function,
            pushed: vec![a],
            pred_pool_seen: vec![0],
            edge_seen: 1,
        }];
        context.predecessor_edge_seen = vec![1];
        let live = crate::engine::CbLiveTerminalSnapshot {
            version: 6,
            comp_ind_bits: 17,
            concept_count: 2,
            concept_names: vec!["A".into(), "B".into()],
            concept_internal: vec![false, false],
            forward_role_succ_trigger: Vec::new(),
            backward_role_succ_trigger: Vec::new(),
            root_concept_order_mode: "incomparable".to_string(),
            non_root_concept_order_mode: "incomparable".to_string(),
            pred_trigger_literals: Vec::new(),
            role_count: 0,
            function_count: 0,
            source_individual_count: 0,
            runtime_individual_count: 0,
            source_ontology: vec![clause.clone()],
            rsucc_enabled: true,
            reach_concept_ids: Vec::new(),
            ordinary_clause_arena: vec![clause],
            root_clause_arena: Vec::new(),
            pending_messages: 0,
            message_truncated: false,
            nominal_truncated: false,
            insertion_history: Vec::new(),
            contexts: vec![context],
        };
        let production = accepted_pred_production();
        let global = serde_json::json!({"send": {
            "version": 2,
            "inter_context": {"production": production.clone()},
            "ground_context_index": null,
            "senders": [],
            "root_sender": null,
            "nominal_allocation": null
        }});
        let candidate = cb_pred_send_coverage_candidate(&global, &live).unwrap();
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent().unwrap().join(".work/artifacts");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join(format!("native-pred-send-{}.json", std::process::id()));
        std::fs::write(&path, serde_json::to_vec(&candidate).unwrap()).unwrap();
        let status = std::process::Command::new(checker).arg(&path).status().unwrap();
        std::fs::remove_file(path).unwrap();
        assert!(status.success());
    }

    #[test]
    fn native_root_pred_send_candidate_passes_real_lean_checker() {
        let Some(checker) = std::env::var_os("KM_CB_TEST_PRED_SEND_COVERAGE_CHECKER") else {
            return;
        };
        let x = crate::calc::X;
        let individual = crate::calc::ind_term(1);
        let b = crate::engine::CbLivePred {
            kind: "concept", iri: 1, first: x, second: None,
        };
        let clause = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&b)],
        };
        let ground_b = crate::engine::CbLivePred {
            first: individual, ..b.clone()
        };
        let ground_clause = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&ground_b)],
        };
        let mut context = live_context(0, 9);
        context.nominal_ground = true;
        context.retained_clause_ids = vec![0, 1];
        context.pred_pool_ids = vec![0, 1];
        context.pred_hwm = 2;
        context.predecessors = vec![crate::engine::CbLivePredecessorEdge {
            predecessor_context: 0,
            label: individual,
            pushed: vec![ground_b],
            pred_pool_seen: vec![0, 1],
            edge_seen: 1,
        }];
        context.predecessor_edge_seen = vec![1];
        let mut live = crate::engine::CbLiveTerminalSnapshot {
            version: 6,
            comp_ind_bits: 17,
            concept_count: 2,
            concept_names: vec!["A".into(), "B".into()],
            concept_internal: vec![false, false],
            forward_role_succ_trigger: Vec::new(),
            backward_role_succ_trigger: Vec::new(),
            root_concept_order_mode: "incomparable".to_string(),
            non_root_concept_order_mode: "incomparable".to_string(),
            pred_trigger_literals: Vec::new(),
            role_count: 0,
            function_count: 0,
            source_individual_count: 2,
            runtime_individual_count: 2,
            source_ontology: vec![clause.clone()],
            rsucc_enabled: true,
            reach_concept_ids: Vec::new(),
            ordinary_clause_arena: Vec::new(),
            root_clause_arena: vec![clause, ground_clause.clone()],
            pending_messages: 0,
            message_truncated: false,
            nominal_truncated: false,
            insertion_history: Vec::new(),
            contexts: vec![context],
        };
        live.insertion_history = vec![
            crate::engine::CbLiveInsertionEvent {
                sequence: 0,
                context_index: 0,
                root: true,
                clause_id: 0,
                origin_hint: "ontology_fact",
                origin_index: Some(0),
                rule_hint: None,
                rule_evidence: None,
            },
            crate::engine::CbLiveInsertionEvent {
                sequence: 1,
                context_index: 0,
                root: true,
                clause_id: 1,
                origin_hint: "derived",
                origin_index: None,
                rule_hint: Some("pred-arrival"),
                rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Pred {
                    sender_context_index: 0,
                    sender_clause_id: 0,
                    edge_label: individual,
                    payload: ground_clause,
                    provider_clause_ids: Vec::new(),
                    matched_predicates: Vec::new(),
                }),
            },
        ];
        let mut production = accepted_pred_production();
        let wire_source_clause = cb_wire_clause(&live.source_ontology[0], live.comp_ind_bits);
        let wire_ground_clause = cb_wire_clause(&live.root_clause_arena[1], live.comp_ind_bits);
        production["source"] = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 2,
            "source_clauses": [{"gci": {"body": [], "head": [1]}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [wire_source_clause.clone()]
        });
        production["individual_count"] = serde_json::json!(2);
        production["contexts"][0]["context_id"] = serde_json::json!(9);
        production["contexts"][0]["root"] = serde_json::json!(true);
        production["contexts"][0]["nominal_ground"] = serde_json::json!(true);
        production["contexts"][0]["core"] = serde_json::json!([]);
        production["contexts"][0]["imports"] = serde_json::json!([wire_ground_clause.clone()]);
        production["contexts"][0]["retained"] =
            serde_json::json!([wire_source_clause.clone(), wire_ground_clause.clone()]);
        production["contexts"][0]["trace"] = serde_json::json!([
            {
                "clause": wire_source_clause,
                "justification": {"premise": {"index": 0, "substitution": []}}
            },
            {
                "clause": wire_ground_clause,
                "justification": {"assumption": {"index": 0}}
            }
        ]);
        let global = serde_json::json!({"send": {
            "version": 2,
            "inter_context": {"production": production.clone()},
            "ground_context_index": null,
            "senders": [],
            "root_sender": null,
            "nominal_allocation": null
        }});
        let candidate = cb_pred_send_coverage_candidate(&global, &live).unwrap();
        assert_eq!(candidate["senders"], serde_json::json!([]));
        assert_eq!(candidate["ground_context_index"], 0);
        assert_eq!(candidate["root_sender"]["transfer_indices"], serde_json::json!([0, 1]));
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent().unwrap().join(".work/artifacts");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join(format!("native-root-pred-send-{}.json", std::process::id()));
        std::fs::write(&path, serde_json::to_vec(&candidate).unwrap()).unwrap();
        let status = std::process::Command::new(checker).arg(&path).status().unwrap();
        assert!(status.success());

        if let Some(root_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_ROOT_PRED_CLOSURE_CHECKER")
        {
            let prior = std::collections::HashMap::from([((0, true, 0), 0)]);
            let pred = cb_pred_event_evidence(&live, &live.insertion_history[1], &prior)
                .expect("exact root Pred arrival evidence");
            let source = production["source"].clone();
            let evidence = vec![serde_json::json!({
                "kind": "seed", "prior_events": [], "trace": [], "discarded": []
            }), pred];
            let root_candidate = cb_source_root_pred_closure_candidate(
                &source, &live, &evidence).expect("construct source-bound root Pred candidate");
            std::fs::write(&path, serde_json::to_vec(&root_candidate).unwrap()).unwrap();
            let root_status = std::process::Command::new(root_checker)
                .arg(&path).status().unwrap();
            assert!(root_status.success(), "native source root Pred closure was rejected");
        }
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn live_publication_rows_cover_the_exact_grouped_answer() {
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.concept_names = vec!["A".to_string(), "B".to_string()];
        live.root_clause_arena = vec![
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![crate::engine::CbLiveLit {
                    kind: "concept",
                    iri: Some(1),
                    first: crate::calc::X,
                    second: None,
                }],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: Vec::new(),
            },
        ];
        live.contexts.truncate(1);
        live.contexts[0].query_concept = Some(0);
        live.contexts[0].retained_clause_ids = vec![0, 1];
        let answer = std::collections::BTreeMap::from([(
            "A".to_string(),
            std::collections::BTreeSet::from([
                "B".to_string(),
                "owl:Nothing".to_string(),
            ]),
        )]);
        let (rows, cells, unsatisfiable) =
            cb_live_publication_rows(&live, &answer).unwrap();
        assert_eq!(rows, vec![serde_json::json!({
            "sub": 0,
            "supers": [1],
            "unsatisfiable": true,
        })]);
        assert_eq!(cells, vec![serde_json::json!({
            "sub": 0,
            "sup": 1,
            "context_index": 0,
        })]);
        assert_eq!(unsatisfiable, vec![serde_json::json!({
            "sub": 0,
            "context_index": 0,
        })]);

        live.contexts[0].retained_clause_ids = vec![1];
        assert!(cb_live_publication_rows(&live, &answer)
            .unwrap_err()
            .contains("no retained unit witness"));

        live.contexts[0].core.clear();
        assert_eq!(
            cb_live_inconsistency_witness(&live).unwrap(),
            serde_json::json!({"context_index": 0})
        );
        live.contexts[0].retained_clause_ids.clear();
        assert!(cb_live_inconsistency_witness(&live).is_err());
    }

    #[test]
    fn exact_taxonomy_candidate_reuses_live_evidence_and_marks_only_negatives() {
        let live = serde_json::json!({
            "version": 1,
            "derivation": {"production_bound": {"live_state": {
                "concept_count": 3,
                "role_count": 0,
                "function_count": 0,
                "source_individual_count": 0,
                "source_ontology": [{
                    "body": [{"kind": "concept", "iri": 0,
                        "first": crate::calc::X, "second": null}],
                    "head": [{"kind": "concept", "iri": 1,
                        "first": crate::calc::X, "second": null}]
                }]
            }}},
            "public_rows": [
                {"sub": 0, "supers": [1], "unsatisfiable": false},
                {"sub": 1, "supers": [], "unsatisfiable": false},
                {"sub": 2, "supers": [], "unsatisfiable": true}
            ],
            "public_subsumptions": [
                {"sub": 0, "sup": 1, "context_index": 0}
            ],
            "unsatisfiable": [
                {"sub": 2, "context_index": 2}
            ]
        });
        let (candidate, unresolved) = cb_exact_taxonomy_candidate(&live).unwrap();
        assert_eq!(candidate["named_concepts"], serde_json::json!([0, 1, 2]));
        assert_eq!(candidate["cells"].as_array().unwrap().len(), 9);
        assert_eq!(unresolved, 0, "all three omitted cells have one-element models");
        assert_eq!(candidate["cells"][0]["evidence"], "reflexive");
        assert_eq!(
            candidate["cells"][1]["evidence"],
            serde_json::json!({"positive": {"live_index": 0}})
        );
        assert!(candidate["cells"][2]["evidence"]["negative"]["model"]
            .is_object());
        assert_eq!(
            candidate["cells"][6]["evidence"],
            serde_json::json!({"unsatisfiable": {"live_index": 0}})
        );
        assert_eq!(candidate["cells"][8]["evidence"], "reflexive");

        let duplicate = serde_json::json!({
            "derivation": {"production_bound": {"live_state": {}}},
            "public_rows": [{"sub": 0}, {"sub": 0}],
            "public_subsumptions": [],
            "unsatisfiable": []
        });
        assert!(cb_exact_taxonomy_candidate(&duplicate)
            .unwrap_err()
            .contains("duplicate subject"));
    }

    #[test]
    fn canonical_binary_role_chains_allocate_finite_fresh_roles() {
        let (target_roles, rules, derivations) = cb_canonical_binary_role_chains(
            5,
            &[(vec![0, 1], 2), (vec![0, 1, 2, 3], 4)],
        )
        .unwrap();
        assert_eq!(target_roles, 7);
        assert_eq!(rules.len(), 4);
        assert_eq!(derivations.len(), 2);
        assert_eq!(
            rules[0],
            serde_json::json!({"first": 0, "second": 1, "conclusion": 2})
        );
        assert_eq!(
            rules[1],
            serde_json::json!({"first": 2, "second": 3, "conclusion": 5})
        );
        assert_eq!(
            rules[2],
            serde_json::json!({"first": 1, "second": 5, "conclusion": 6})
        );
        assert_eq!(
            rules[3],
            serde_json::json!({"first": 0, "second": 6, "conclusion": 4})
        );
        assert_eq!(derivations[0]["compose"]["rule"], 0);
        assert_eq!(derivations[1]["compose"]["rule"], 3);
    }

    #[test]
    fn canonical_binary_role_chains_reject_malformed_sources() {
        assert!(cb_canonical_binary_role_chains(2, &[(vec![0], 1)])
            .unwrap_err()
            .contains("fewer than two"));
        assert!(cb_canonical_binary_role_chains(2, &[(vec![0, 2], 1)])
            .unwrap_err()
            .contains("exceeds"));
        assert!(cb_canonical_binary_role_chains(2, &[(vec![0, 1], 2)])
            .unwrap_err()
            .contains("exceeds"));
    }

    #[test]
    fn certified_typed_source_maps_exactly_to_arbitrary_chain_safe_wire() {
        let source = serde_json::json!({
            "version": 1,
            "concept_count": 4,
            "role_count": 3,
            "function_count": 1,
            "individual_count": 1,
            "source_clauses": [
                {"gci": {"body": [0], "head": [1, 2]}},
                {"exR": {"source": 0, "role": 0, "filler": 1}},
                {"allR": {"source": 1, "role": 1, "filler": 2}},
                {"exL": {"role": 1, "filler": 2, "conclusion": 3}},
                {"subR": {"sub": 0, "sup": 1}},
                {"inverse": {"role": 1, "inverse": 2}},
                {"functional": {"role": 2}},
                {"nominal": {"concept": 3, "individual": 0}},
                {"atMost": {"cardinality": 2, "role": 0, "concept": 1}}
            ],
            "role_chains": [{"body": [0, 1, 2], "sup": 2}],
            "role_axioms": [],
            "ontology": []
        });
        let global = serde_json::json!({
            "left": {"source": source.clone()},
            "right": [{"nested": {"source": source}}]
        });
        let safe = cb_regular_arbitrary_chain_source(&global).unwrap();
        assert_eq!(safe.concept_count, 4);
        assert_eq!(safe.role_count, 3);
        assert_eq!(safe.individual_count, 1);
        assert_eq!(safe.chains, vec![serde_json::json!({
            "body": [0, 1, 2], "sup": 2
        })]);
        assert_eq!(safe.clauses[0], serde_json::json!({
            "core": {"clause": {"base": {"clause": {
                "gci": {"body": [0], "head": [1, 2]}
            }}}}
        }));
        assert_eq!(safe.clauses[5], serde_json::json!({
            "core": {"clause": {"base": {"clause": {
                "inv": {"role": 1, "inverse": 2}
            }}}}
        }));
        assert_eq!(safe.clauses[6], serde_json::json!({"func": {"role": 2}}));
        assert_eq!(safe.clauses[7], serde_json::json!({
            "core": {"clause": {"nominal": {"clause": {
                "concept": 3, "individual": 0
            }}}}
        }));
        assert_eq!(safe.clauses[8], serde_json::json!({
            "atMost": {"bound": 2, "role": 0, "filler": 1}
        }));
    }

    #[test]
    fn source_exact_taxonomy_uses_real_production_traces_and_models() {
        let checker = std::env::var_os("KM_CB_TEST_SOURCE_EXACT_TAXONOMY_CHECKER")
            .expect("the source-exact taxonomy test requires the real Lean checker");
        let context_checker =
            std::env::var_os("KM_CB_TEST_STANDALONE_CONTEXT_PROOF_CHECKER")
                .expect("the standalone context test requires the real Lean checker");
        let production_checker =
            std::env::var_os("KM_CB_TEST_SOURCE_PRODUCTION_TAXONOMY_CHECKER")
                .expect("the shared-production taxonomy test requires the real Lean checker");
        let term = |variable: i64| serde_json::json!({"var": {"index": variable}});
        let concept = |id: usize| serde_json::json!({"predicate": {"predicate": {
            "concept": {"concept": id, "term": term(0)}
        }}});
        let unit = |id: usize| serde_json::json!({"body": [], "head": [concept(id)]});
        let gci = serde_json::json!({"body": [concept(0)], "head": [concept(1)]});
        let live_concept = |id: usize| serde_json::json!({
            "kind": "concept", "iri": id,
            "first": crate::calc::X, "second": null
        });
        let live_unit = |id: usize| serde_json::json!({
            "body": [], "head": [live_concept(id)]
        });
        let live_gci = serde_json::json!({
            "body": [live_concept(0)], "head": [live_concept(1)]
        });
        let source = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [{"gci": {"body": [0], "head": [1]}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [gci]
        });
        let live_state = serde_json::json!({
            "comp_ind_bits": 17,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "source_individual_count": 0,
            "concept_names": ["A", "B"],
            "source_ontology": [live_gci],
            "ordinary_clause_arena": [],
            "root_clause_arena": [live_unit(0), live_unit(1)],
            "contexts": [
                {"root": true, "query_concept": 0, "core": [live_concept(0)],
                 "retained_clause_ids": [0, 1]},
                {"root": true, "query_concept": 1, "core": [live_concept(1)],
                 "retained_clause_ids": [1]}
            ],
            "insertion_history": [
                {"sequence": 0, "context_index": 0, "root": true,
                 "clause_id": 0, "origin_hint": "core", "origin_index": 0},
                {"sequence": 1, "context_index": 0, "root": true,
                 "clause_id": 1, "origin_hint": "derived", "origin_index": null},
                {"sequence": 2, "context_index": 1, "root": true,
                 "clause_id": 1, "origin_hint": "core", "origin_index": 0}
            ]
        });
        let publication = serde_json::json!({
            "derivation": {
                "production_bound": {
                    "global_model": {"source": source},
                    "live_state": live_state
                },
                "insertion_evidence": [
                    {"kind": "seed", "prior_events": [], "trace": [], "discarded": []},
                    {"kind": "local", "prior_events": [{"event_index": 0}],
                     "trace": [
                        {"clause": gci, "justification": {"premise": {
                            "index": 0, "substitution": []
                        }}},
                        {"clause": unit(1), "justification": {"resolve": {
                            "positive": 0, "negative": 1, "literal": concept(0)
                        }}}
                     ], "discarded": []},
                    {"kind": "seed", "prior_events": [], "trace": [], "discarded": []}
                ]
            },
            "public_rows": [
                {"sub": 0, "supers": [0, 1], "unsatisfiable": false},
                {"sub": 1, "supers": [1], "unsatisfiable": false}
            ],
            "public_subsumptions": [
                {"sub": 0, "sup": 0, "context_index": 0},
                {"sub": 0, "sup": 1, "context_index": 0},
                {"sub": 1, "sup": 1, "context_index": 1}
            ],
            "unsatisfiable": []
        });
        let (mut candidate, unresolved) = cb_source_exact_taxonomy_candidate(&publication)
            .expect("construct the standalone source-exact taxonomy");
        assert_eq!(unresolved, 0);
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join(".work/artifacts")
            .join(format!("cb-source-exact-test-{}.json", std::process::id()));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let proof_path = path.with_extension("context.json");
        let production_path = path.with_extension("production.json");
        let witness_events = cb_public_witness_events(&publication).unwrap();
        let (context_document, event_nodes) =
            cb_standalone_context_proof_document(&publication, &witness_events).unwrap();
        assert_eq!(event_nodes.len(), 3, "the shared DAG must deduplicate witnesses");
        std::fs::write(&proof_path, serde_json::to_vec(&context_document).unwrap()).unwrap();
        assert!(
            std::process::Command::new(&context_checker)
                .arg(&proof_path)
                .status()
                .unwrap()
                .success(),
            "Lean must accept the native chronological context proof"
        );
        let (mut production_document, production_unresolved) =
            cb_source_production_taxonomy_candidate(&publication).unwrap();
        assert_eq!(production_unresolved, 0);
        std::fs::write(
            &production_path,
            serde_json::to_vec(&production_document).unwrap(),
        )
        .unwrap();
        assert!(
            std::process::Command::new(&production_checker)
                .arg(&production_path)
                .status()
                .unwrap()
                .success(),
            "Lean must accept the joint source, shared DAG, and matrix"
        );
        production_document["cells"][1]["evidence"] =
            serde_json::json!({"positiveNode": {"node": 0}});
        std::fs::write(
            &production_path,
            serde_json::to_vec(&production_document).unwrap(),
        )
        .unwrap();
        assert!(
            !std::process::Command::new(&production_checker)
                .arg(&production_path)
                .status()
                .unwrap()
                .success(),
            "Lean must reject a matrix cell redirected to the wrong shared node"
        );
        std::fs::write(&path, serde_json::to_vec(&candidate).unwrap()).unwrap();
        let accepted = std::process::Command::new(&checker)
            .arg(&path)
            .status()
            .unwrap()
            .success();
        assert!(accepted, "Lean must accept the exact production trace and countermodel matrix");
        let regular_source = cb_regular_arbitrary_chain_source(
            publication.pointer("/derivation/production_bound/global_model").unwrap(),
        )
        .unwrap();
        let regular = cb_regular_arbitrary_chain_countermodel(&regular_source, 1, 0)
            .unwrap()
            .expect("the empty role source has a regular B-not-A model");
        candidate["taxonomy"]["cells"][2]["evidence"] =
            serde_json::json!({"regularArbitraryChain": {"model": regular}});
        std::fs::write(&path, serde_json::to_vec(&candidate).unwrap()).unwrap();
        assert!(
            std::process::Command::new(&checker)
                .arg(&path)
                .status()
                .unwrap()
                .success(),
            "the source-bound taxonomy checker must accept regular negative evidence"
        );
        let mut forged = candidate;
        forged["taxonomy"]["published"][2] = serde_json::json!(true);
        std::fs::write(&path, serde_json::to_vec(&forged).unwrap()).unwrap();
        let rejected = !std::process::Command::new(checker)
            .arg(&path)
            .status()
            .unwrap()
            .success();
        assert!(rejected, "Lean must reject a forged source-exact publication bit");
        let _ = std::fs::remove_file(path);
        let _ = std::fs::remove_file(proof_path);
        let _ = std::fs::remove_file(production_path);
    }

    #[test]
    fn certified_typed_source_rejects_disagreeing_embedded_runs() {
        let source = |concept_count| serde_json::json!({
            "version": 1,
            "concept_count": concept_count,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [],
            "role_chains": [],
            "role_axioms": [],
            "ontology": []
        });
        let forged = serde_json::json!({
            "first": source(1),
            "second": source(2),
        });
        assert!(cb_regular_arbitrary_chain_source(&forged)
            .unwrap_err()
            .contains("disagreeing"));
    }

    #[test]
    fn native_regular_countermodel_passes_the_exact_lean_wire_checker() {
        let Some(checker) = std::env::var_os("KM_CB_TEST_REGULAR_ARBITRARY_CHAIN_CHECKER")
        else {
            return;
        };
        let binding = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [],
            "role_chains": [],
            "role_axioms": [],
            "ontology": []
        });
        let source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": binding}}),
        )
        .unwrap();
        let countermodel = cb_regular_arbitrary_chain_countermodel(&source, 0, 1)
            .expect("construct the native regular countermodel")
            .expect("the empty source does not entail concept 0 below concept 1");
        let mut document = serde_json::json!({
            "concept_count": source.concept_count,
            "role_count": source.role_count,
            "function_count": 0,
            "individual_count": source.individual_count,
            "source": source.source_ontology,
            "sub": 0,
            "sup": 1,
            "countermodel": countermodel,
        });
        let artifact_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("engine has a repository parent")
            .join(".work/artifacts");
        std::fs::create_dir_all(&artifact_root).unwrap();
        let path = artifact_root.join(format!(
            "cb-regular-arbitrary-chain-test-{}.json",
            std::process::id()
        ));
        let check = |value: &serde_json::Value| {
            std::fs::write(&path, serde_json::to_vec(value).unwrap()).unwrap();
            std::process::Command::new(&checker)
                .arg(&path)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .expect("run the dedicated Lean countermodel checker")
                .success()
        };
        assert!(check(&document), "Lean must accept the native countermodel");

        let term = |index| serde_json::json!({"var": {"index": index}});
        let role_literal = |role, source, target| serde_json::json!({
            "predicate": {"predicate": {"role": {
                "role": role, "source": term(source), "target": term(target)
            }}}
        });
        let chain_binding = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 3,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [],
            "role_chains": [{"body": [0, 1, 2], "sup": 2}],
            "role_axioms": [],
            "ontology": [{
                "body": [
                    role_literal(0, 0, -1),
                    role_literal(1, -1, -2),
                    role_literal(2, -2, -3)
                ],
                "head": [role_literal(2, 0, -3)]
            }]
        });
        let chain_source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": chain_binding}}),
        )
        .unwrap();
        let chain_countermodel =
            cb_regular_arbitrary_chain_countermodel(&chain_source, 0, 1)
                .expect("construct an arbitrary-chain countermodel")
                .expect("the role-only source does not entail the concept query");
        document = serde_json::json!({
            "concept_count": chain_source.concept_count,
            "role_count": chain_source.role_count,
            "function_count": 0,
            "individual_count": chain_source.individual_count,
            "source": chain_source.source_ontology,
            "sub": 0,
            "sup": 1,
            "countermodel": chain_countermodel,
        });
        assert!(
            check(&document),
            "Lean must accept the native arbitrary-chain countermodel"
        );

        let functional_binding = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 1,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [{"functional": {"role": 0}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [{
                "body": [
                    role_literal(0, 0, -1),
                    role_literal(0, 0, -2)
                ],
                "head": [{"equality": {
                    "left": term(-1), "right": term(-2)
                }}]
            }]
        });
        let functional_source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": functional_binding}}),
        )
        .unwrap();
        let functional_countermodel =
            cb_regular_arbitrary_chain_countermodel(&functional_source, 0, 1)
                .expect("construct a functionality countermodel")
                .expect("functionality does not entail the concept query");
        document = serde_json::json!({
            "concept_count": functional_source.concept_count,
            "role_count": functional_source.role_count,
            "function_count": 0,
            "individual_count": functional_source.individual_count,
            "source": functional_source.source_ontology,
            "sub": 0,
            "sup": 1,
            "countermodel": functional_countermodel,
        });
        assert!(
            check(&document),
            "Lean must accept the native functionality countermodel"
        );

        let multi_functional_binding = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 2,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [
                {"functional": {"role": 0}},
                {"functional": {"role": 1}}
            ],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [
                {
                    "body": [role_literal(0, 0, -1), role_literal(0, 0, -2)],
                    "head": [{"equality": {"left": term(-1), "right": term(-2)}}]
                },
                {
                    "body": [role_literal(1, 0, -1), role_literal(1, 0, -2)],
                    "head": [{"equality": {"left": term(-1), "right": term(-2)}}]
                }
            ]
        });
        let multi_source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": multi_functional_binding}}),
        )
        .unwrap();
        let multi_countermodel =
            cb_regular_arbitrary_chain_countermodel(&multi_source, 0, 1)
                .expect("construct a repeated-definition countermodel")
                .expect("two functional roles do not entail the concept query");
        document = serde_json::json!({
            "concept_count": multi_source.concept_count,
            "role_count": multi_source.role_count,
            "function_count": 0,
            "individual_count": multi_source.individual_count,
            "source": multi_source.source_ontology,
            "sub": 0,
            "sup": 1,
            "countermodel": multi_countermodel,
        });
        assert!(
            check(&document),
            "Lean must accept repeated universal-marker definitions"
        );

        let concept_literal = |concept, value| serde_json::json!({
            "predicate": {"predicate": {"concept": {
                "concept": concept, "term": value
            }}}
        });
        let gci_binding = serde_json::json!({
            "version": 1,
            "concept_count": 3,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [{"gci": {"body": [0], "head": [1]}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [{
                "body": [concept_literal(0, term(0))],
                "head": [concept_literal(1, term(0))]
            }]
        });
        let gci_source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": gci_binding}}),
        )
        .unwrap();
        let gci_countermodel = cb_regular_arbitrary_chain_countermodel(&gci_source, 0, 2)
            .expect("construct a GCI countermodel")
            .expect("the GCI does not entail the unrelated concept query");
        document = serde_json::json!({
            "concept_count": gci_source.concept_count,
            "role_count": gci_source.role_count,
            "function_count": 0,
            "individual_count": gci_source.individual_count,
            "source": gci_source.source_ontology,
            "sub": 0,
            "sup": 2,
            "countermodel": gci_countermodel,
        });
        assert!(
            check(&document),
            "Lean must accept the native core-GCI countermodel"
        );

        let individual_zero = serde_json::json!({"constant": {"individual": 0}});
        let nominal_binding = serde_json::json!({
            "version": 1,
            "concept_count": 3,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 1,
            "source_clauses": [{"nominal": {"concept": 0, "individual": 0}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [
                {
                    "body": [concept_literal(0, term(0))],
                    "head": [{"equality": {
                        "left": term(0),
                        "right": {"constant": {"individual": 0}}
                    }}]
                },
                {
                    "body": [],
                    "head": [concept_literal(0, individual_zero)]
                }
            ]
        });
        let nominal_source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": nominal_binding}}),
        )
        .unwrap();
        let nominal_countermodel = cb_regular_arbitrary_chain_countermodel(&nominal_source, 1, 2)
            .expect("construct a nominal countermodel")
            .expect("the nominal source does not entail the unrelated concept query");
        document = serde_json::json!({
            "concept_count": nominal_source.concept_count,
            "role_count": nominal_source.role_count,
            "function_count": 0,
            "individual_count": nominal_source.individual_count,
            "source": nominal_source.source_ontology,
            "sub": 1,
            "sup": 2,
            "countermodel": nominal_countermodel,
        });
        assert!(
            check(&document),
            "Lean must accept the native nominal-root countermodel"
        );
        document["countermodel"]["individual_roots"] = serde_json::json!([]);
        assert!(
            !check(&document),
            "Lean must reject a countermodel with a forged nominal-root assignment"
        );
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn typed_regular_cardinality_countermodel_respects_function_allocation() {
        let Some(checker) =
            std::env::var_os("KM_CB_TEST_TYPED_REGULAR_ARBITRARY_CHAIN_CHECKER")
        else {
            return;
        };
        use crate::frontend::{clauses::clause_to_json, iri::IriRegistry, normalise, parse};

        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(
            &mut registry,
            "Ontology(\
              SubClassOf(<A> ObjectMinCardinality(2 <R> <B>))\
              SubClassOf(<A> ObjectMaxCardinality(2 <R> <B>)))",
        )
        .expect("parse mixed guarded cardinality source");
        let (clauses, _, _) = normalise::normalise(&ontology);
        let clauses = clauses.iter().map(clause_to_json).collect::<Vec<_>>();
        let binding = crate::cb_source::typed_source_candidate(&clauses)
            .expect("compile the exact allocated typed source");
        let production = crate::reasoner::cb_production_input(&clauses);
        let sub = production
            .concept_names
            .iter()
            .position(|name| name == "B")
            .expect("B concept id");
        let sup = production
            .concept_names
            .iter()
            .position(|name| name == "A")
            .expect("A concept id");
        let source = cb_regular_arbitrary_chain_source(
            &serde_json::json!({"production": {"source": binding.clone()}}),
        )
        .expect("translate the guarded cardinality source");
        assert!(source
            .clauses
            .iter()
            .any(|clause| clause.get("atLeast").is_some()));
        assert!(source
            .clauses
            .iter()
            .any(|clause| clause.get("guardedAtMost").is_some()));
        let countermodel = cb_regular_arbitrary_chain_countermodel(&source, sub, sup)
            .expect("construct the typed regular cardinality countermodel")
            .expect("B is not subsumed by A");
        let mut document = serde_json::json!({
            "source": binding,
            "sub": sub,
            "sup": sup,
            "countermodel": countermodel,
        });
        let artifact_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("engine has a repository parent")
            .join(".work/artifacts");
        std::fs::create_dir_all(&artifact_root).unwrap();
        let path = artifact_root.join(format!(
            "cb-typed-regular-cardinality-test-{}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&document).unwrap()).unwrap();
        let output = std::process::Command::new(&checker)
            .arg(&path)
            .output()
            .expect("run the typed regular Lean checker");
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let production_count = document["source"]["function_allocation"]["production_count"]
            .as_u64()
            .expect("production function count");
        document["source"]["function_allocation"]["sparse_allocation"][0]["target"] =
            serde_json::json!(production_count);
        std::fs::write(&path, serde_json::to_vec(&document).unwrap()).unwrap();
        let forged = std::process::Command::new(&checker)
            .arg(&path)
            .output()
            .expect("run the typed regular Lean checker on forged allocation");
        assert!(
            !forged.status.success(),
            "Lean must reject a typed countermodel whose production function allocation was forged"
        );
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn one_element_countermodel_respects_equality_and_inequality_truth() {
        let state = serde_json::json!({
            "concept_count": 2,
            "role_count": 1,
            "function_count": 1,
            "source_individual_count": 1,
            "source_ontology": [
                {"body": [{"kind": "equality", "iri": null,
                    "first": crate::calc::X, "second": crate::calc::X}],
                 "head": [{"kind": "concept", "iri": 0,
                    "first": crate::calc::X, "second": null}]},
                {"body": [{"kind": "inequality", "iri": null,
                    "first": crate::calc::X, "second": crate::calc::X}],
                 "head": []},
                {"body": [],
                 "head": [{"kind": "equality", "iri": null,
                    "first": crate::calc::X, "second": crate::calc::FTERM_BASE}]}
            ]
        });
        let model = cb_one_element_countermodel(&state, 0, 1)
            .unwrap()
            .expect("A and not-B have a one-element model");
        assert_eq!(model["domain_size"], 1);
        assert_eq!(model["concepts"], serde_json::json!([[true], [false]]));
        assert_eq!(model["roles"], serde_json::json!([[[false]]]));
        assert_eq!(model["constants"], serde_json::json!([0]));
        assert_eq!(model["functions"], serde_json::json!([[0]]));

        let impossible = serde_json::json!({
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "source_individual_count": 0,
            "source_ontology": [{
                "body": [{"kind": "concept", "iri": 0,
                    "first": crate::calc::X, "second": null}],
                "head": [{"kind": "inequality", "iri": null,
                    "first": crate::calc::X, "second": crate::calc::X}]
            }]
        });
        assert!(cb_one_element_countermodel(&impossible, 0, 1)
            .unwrap()
            .is_none());
    }

    #[test]
    fn two_element_countermodel_closes_a_genuine_inequality_model() {
        let first = crate::calc::X + 1;
        let second = crate::calc::X + 2;
        let state = serde_json::json!({
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "source_individual_count": 3,
            "source_ontology": [{
                "body": [],
                "head": [{"kind": "inequality", "iri": null,
                    "first": first, "second": second}]
            }]
        });
        assert!(cb_finite_countermodel(&state, 0, 1, 1)
            .unwrap()
            .is_none());
        let model = cb_finite_countermodel(&state, 0, 1, 2)
            .unwrap()
            .expect("two distinct constants need and admit two elements");
        assert_eq!(model["domain_size"], 2);
        assert_ne!(model["constants"][1], model["constants"][2]);
        assert_eq!(model["concepts"][0][0], true);
        assert_eq!(model["concepts"][1][0], false);
    }

    #[test]
    fn two_element_countermodel_grounds_functions_over_every_value() {
        let state = serde_json::json!({
            "concept_count": 2,
            "role_count": 0,
            "function_count": 2,
            "source_individual_count": 0,
            "source_ontology": [{
                "body": [],
                "head": [{"kind": "inequality", "iri": null,
                    "first": crate::calc::X,
                    "second": crate::calc::FTERM_BASE + 1}]
            }]
        });
        assert!(cb_finite_countermodel(&state, 0, 1, 1)
            .unwrap()
            .is_none());
        let model = cb_finite_countermodel(&state, 0, 1, 2)
            .unwrap()
            .expect("a fixed-point-free unary function exists on two elements");
        assert_eq!(model["functions"][1], serde_json::json!([1, 0]));
    }

    #[test]
    fn blocked_taxonomy_countermodel_builds_a_closed_resolution_trace() {
        let publication = serde_json::json!({
            "derivation": {"production_bound": {
                "live_state": {"concept_count": 3, "role_count": 0},
                "global_model": {"blocked_saturation": {"saturation": {
                    "atom_count": 4,
                    "premises": [{"neg": [0], "pos": [2]}]
                }}}
            }}
        });
        let countermodel = cb_blocked_taxonomy_countermodel(&publication, 0, 1)
            .unwrap()
            .expect("A implies C remains compatible with A and not-B");
        assert_eq!(countermodel["witness"], 0);
        assert_eq!(
            countermodel["saturation"]["premises"],
            serde_json::json!([
                {"neg": [0], "pos": [2]},
                {"neg": [], "pos": [0]},
                {"neg": [1], "pos": []}
            ])
        );
        assert!(countermodel["saturation"]["trace"]
            .as_array()
            .unwrap()
            .iter()
            .any(|step| step["clause"] == serde_json::json!({"neg": [], "pos": [2]})));
    }

    #[test]
    fn blocked_taxonomy_countermodel_rejects_a_refuted_query() {
        let publication = serde_json::json!({
            "derivation": {"production_bound": {
                "live_state": {"concept_count": 2, "role_count": 0},
                "global_model": {"blocked_saturation": {"saturation": {
                    "atom_count": 3,
                    "premises": [{"neg": [0], "pos": [1]}]
                }}}
            }}
        });
        assert!(cb_blocked_taxonomy_countermodel(&publication, 0, 1)
            .unwrap()
            .is_none());
    }

    #[test]
    fn factor_metadata_builds_a_chronological_checked_trace() {
        let equality = |left, right| crate::engine::CbLiveLit {
            kind: "equality",
            iri: None,
            first: left,
            second: Some(right),
        };
        let inequality = |left, right| crate::engine::CbLiveLit {
            kind: "inequality",
            iri: None,
            first: left,
            second: Some(right),
        };
        let common = crate::calc::FTERM_BASE;
        let first = crate::calc::FTERM_BASE + 1;
        let second = crate::calc::FTERM_BASE + 2;
        let source = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![equality(common, first), equality(common, second)],
        };
        let result = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![equality(common, second), inequality(first, second)],
        };
        let mut live = live_snapshot();
        live.function_count = 3;
        live.root_clause_arena = vec![source, result];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 1,
            context_index: 0,
            root: true,
            clause_id: 1,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("factor"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Factor {
                source_clause_id: 0,
                common,
                first,
                second,
            }),
        };
        let prior = std::collections::HashMap::from([((0, true, 0), 0)]);
        let evidence = cb_factor_event_evidence(&live, &event, &prior).unwrap();
        assert_eq!(evidence["kind"], "local");
        assert_eq!(evidence["prior_events"][0]["event_index"], 0);
        assert!(evidence["trace"][0]["justification"]["factor"].is_object());
    }

    #[test]
    fn paramodulation_metadata_builds_a_chronological_checked_trace() {
        let equality = |left, right| crate::engine::CbLiveLit {
            kind: "equality",
            iri: None,
            first: left,
            second: Some(right),
        };
        let concept = |iri, term| crate::engine::CbLiveLit {
            kind: "concept",
            iri: Some(iri),
            first: term,
            second: None,
        };
        let left = crate::calc::FTERM_BASE;
        let right = crate::calc::FTERM_BASE + 1;
        let rewritten_literal = concept(0, left);
        let equality_clause = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![equality(left, right)],
        };
        let other_clause = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![rewritten_literal.clone()],
        };
        let result = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![concept(0, right)],
        };
        let mut live = live_snapshot();
        live.concept_count = 1;
        live.function_count = 2;
        live.root_clause_arena = vec![equality_clause, other_clause, result];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 2,
            context_index: 0,
            root: true,
            clause_id: 2,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("eq"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Paramodulate {
                equality_clause_id: 0,
                other_clause_id: 1,
                left,
                right,
                literal: rewritten_literal,
            }),
        };
        let prior = std::collections::HashMap::from([((0, true, 0), 0), ((0, true, 1), 1)]);
        let evidence = cb_paramodulate_event_evidence(&live, &event, &prior).unwrap();
        assert_eq!(evidence["kind"], "local");
        assert_eq!(evidence["prior_events"][0]["event_index"], 0);
        assert_eq!(evidence["prior_events"][1]["event_index"], 1);
        assert!(evidence["trace"][0]["justification"]["paramodulate"].is_object());
    }

    #[test]
    fn paramodulation_trace_exposes_folded_reflexive_inequality_deletion() {
        let binary = |kind, left, right| crate::engine::CbLiveLit {
            kind,
            iri: None,
            first: left,
            second: Some(right),
        };
        let left = crate::calc::FTERM_BASE;
        let right = crate::calc::FTERM_BASE + 1;
        let target = binary("inequality", left, right);
        let mut live = live_snapshot();
        live.function_count = 2;
        live.root_clause_arena = vec![
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![binary("equality", left, right)],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![target.clone()],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: Vec::new(),
            },
        ];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 2,
            context_index: 0,
            root: true,
            clause_id: 2,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("eq"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Paramodulate {
                equality_clause_id: 0,
                other_clause_id: 1,
                left,
                right,
                literal: target,
            }),
        };
        let prior = std::collections::HashMap::from([((0, true, 0), 0), ((0, true, 1), 1)]);
        let evidence = cb_paramodulate_event_evidence(&live, &event, &prior).unwrap();
        assert_eq!(evidence["trace"].as_array().unwrap().len(), 2);
        assert!(evidence["trace"][1]["justification"]["deleteReflexiveInequality"].is_object());
    }

    #[test]
    fn join_resolution_metadata_builds_a_checked_trace() {
        let individual = crate::calc::X + 1;
        let predicate = crate::engine::CbLivePred {
            kind: "concept",
            iri: 0,
            first: individual,
            second: None,
        };
        let literal = cb_live_pred_literal(&predicate);
        let mut live = live_snapshot();
        live.source_individual_count = 1;
        live.runtime_individual_count = 1;
        live.root_clause_arena = vec![
            crate::engine::CbLiveClause {
                body: vec![literal.clone()],
                head: Vec::new(),
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![literal],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: Vec::new(),
            },
        ];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 2,
            context_index: 0,
            root: true,
            clause_id: 2,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("join"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::JoinResolve {
                consumer_clause_id: 0,
                provider_clause_id: 1,
                ground: predicate,
            }),
        };
        let prior = std::collections::HashMap::from([((0, true, 0), 0), ((0, true, 1), 1)]);
        let evidence = cb_join_event_evidence(&live, &event, &prior).unwrap();
        assert!(evidence["trace"][0]["justification"]["resolve"].is_object());
    }

    #[test]
    fn join3_metadata_builds_a_checked_three_premise_trace() {
        let individual = crate::calc::X + 1;
        let predicate = |iri, term| crate::engine::CbLivePred {
            kind: "concept",
            iri,
            first: term,
            second: None,
        };
        let ground = predicate(0, individual);
        let general = predicate(0, crate::calc::X);
        let conclusion = cb_live_pred_literal(&predicate(1, crate::calc::X));
        let bridge = crate::engine::CbLiveLit {
            kind: "equality",
            iri: None,
            first: individual,
            second: Some(crate::calc::X),
        };
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.source_individual_count = 1;
        live.runtime_individual_count = 1;
        live.root_clause_arena = vec![
            crate::engine::CbLiveClause {
                body: vec![cb_live_pred_literal(&ground)],
                head: vec![conclusion.clone()],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![cb_live_pred_literal(&general)],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![bridge],
            },
            crate::engine::CbLiveClause {
                body: Vec::new(),
                head: vec![conclusion],
            },
        ];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 3,
            context_index: 0,
            root: true,
            clause_id: 3,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("join"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Join3 {
                consumer_clause_id: 0,
                provider_clause_id: 1,
                bridge_clause_id: 2,
                ground,
                general,
                term: individual,
            }),
        };
        let prior = std::collections::HashMap::from([
            ((0, true, 0), 0),
            ((0, true, 1), 1),
            ((0, true, 2), 2),
        ]);
        let evidence = cb_join_event_evidence(&live, &event, &prior).unwrap();
        assert_eq!(evidence["prior_events"].as_array().unwrap().len(), 3);
        assert!(evidence["trace"][0]["justification"]["join3"].is_object());
    }

    #[test]
    fn pred_metadata_cites_exact_sender_and_provider_events() {
        let predicate = |iri| crate::engine::CbLivePred {
            kind: "concept",
            iri,
            first: crate::calc::X,
            second: None,
        };
        let premise = predicate(0);
        let conclusion = predicate(1);
        let payload = crate::engine::CbLiveClause {
            body: vec![cb_live_pred_literal(&premise)],
            head: vec![cb_live_pred_literal(&conclusion)],
        };
        let provider = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&premise)],
        };
        let result = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&conclusion)],
        };
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.root_clause_arena = vec![payload.clone(), provider, result];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 2,
            context_index: 1,
            root: true,
            clause_id: 2,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("pred-arrival"),
            rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Pred {
                sender_context_index: 0,
                sender_clause_id: 0,
                edge_label: crate::calc::X,
                payload,
                provider_clause_ids: vec![1],
                matched_predicates: vec![premise],
            }),
        };
        let prior = std::collections::HashMap::from([((0, true, 0), 0), ((1, true, 1), 1)]);
        let evidence = cb_pred_event_evidence(&live, &event, &prior).unwrap();
        assert_eq!(evidence["kind"], "pred");
        assert_eq!(evidence["sender_event"]["event_index"], 0);
        assert_eq!(evidence["provider_events"][0]["event_index"], 1);
        assert_eq!(evidence["edge_label"], cb_wire_term(crate::calc::X, 17));
        assert_eq!(evidence["payload"]["body"].as_array().unwrap().len(), 1);
        assert_eq!(evidence["matched_predicates"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn native_source_live_pred_candidate_passes_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_LIVE_DERIVATION_CHECKER")
        else {
            return;
        };
        let fact = crate::engine::CbLivePred {
            kind: "concept",
            iri: 0,
            first: crate::calc::X,
            second: None,
        };
        let unit = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&fact)],
        };
        let mut live = live_snapshot();
        live.root_clause_arena = vec![unit.clone(), unit.clone()];
        live.source_ontology = vec![unit.clone()];
        live.contexts[0].retained_clause_ids = vec![0];
        live.contexts[0].pred_pool_ids = vec![0];
        live.contexts[0].pred_hwm = 1;
        live.contexts[1].retained_clause_ids = vec![1];
        live.contexts[1].pred_pool_ids = vec![1];
        live.contexts[1].pred_hwm = 1;
        live.insertion_history = vec![
            crate::engine::CbLiveInsertionEvent {
                sequence: 0,
                context_index: 0,
                root: true,
                clause_id: 0,
                origin_hint: "ontology_fact",
                origin_index: Some(0),
                rule_hint: None,
                rule_evidence: None,
            },
            crate::engine::CbLiveInsertionEvent {
                sequence: 1,
                context_index: 1,
                root: true,
                clause_id: 1,
                origin_hint: "derived",
                origin_index: None,
                rule_hint: Some("pred-arrival"),
                rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Pred {
                    sender_context_index: 0,
                    sender_clause_id: 0,
                    edge_label: crate::calc::X,
                    payload: unit.clone(),
                    provider_clause_ids: Vec::new(),
                    matched_predicates: Vec::new(),
                }),
            },
        ];
        let prior = std::collections::HashMap::from([((0, true, 0), 0)]);
        let pred = cb_pred_event_evidence(&live, &live.insertion_history[1], &prior)
            .expect("exact source-bound Pred evidence");
        let source = serde_json::json!({
            "version": 1,
            "concept_count": 1,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [{"gci": {"body": [], "head": [0]}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [cb_wire_clause(&unit, live.comp_ind_bits)],
        });
        let evidence = vec![
            serde_json::json!({
                "kind": "seed", "prior_events": [], "trace": [], "discarded": []
            }),
            pred,
        ];
        let candidate = cb_source_live_derivation_candidate(&source, &live, &evidence)
            .expect("source-bound live candidate");
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent().unwrap().join(".work/artifacts")
            .join(format!("cb-source-live-pred-{}.json", std::process::id()));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, serde_json::to_vec(&candidate).unwrap()).unwrap();
        let status = std::process::Command::new(&checker).arg(&path).status().unwrap();
        assert!(status.success(), "source-bound live Pred candidate was rejected");

        let mut pending = candidate.clone();
        pending["pending_messages"] = serde_json::json!(1);
        std::fs::write(&path, serde_json::to_vec(&pending).unwrap()).unwrap();
        let pending_status = std::process::Command::new(&checker)
            .arg(&path).status().unwrap();
        assert!(!pending_status.success(),
            "source-bound live checker accepted pending messages");

        let mut dirty = candidate.clone();
        dirty["contexts"][0]["dirty"] = serde_json::json!(true);
        std::fs::write(&path, serde_json::to_vec(&dirty).unwrap()).unwrap();
        let dirty_status = std::process::Command::new(&checker)
            .arg(&path).status().unwrap();
        assert!(!dirty_status.success(),
            "source-bound live checker accepted a dirty context");

        let mut missing_pool_entry = candidate.clone();
        missing_pool_entry["contexts"][0]["pred_pool_ids"] = serde_json::json!([]);
        missing_pool_entry["contexts"][0]["pred_hwm"] = serde_json::json!(0);
        std::fs::write(&path, serde_json::to_vec(&missing_pool_entry).unwrap()).unwrap();
        let missing_pool_status = std::process::Command::new(&checker)
            .arg(&path).status().unwrap();
        assert!(!missing_pool_status.success(),
            "source-bound live checker accepted a missing eligible Pred-pool entry");

        if let Some(local_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_LOCAL_CLOSURE_CHECKER")
        {
            let local = serde_json::json!({"version": 1, "live": candidate});
            std::fs::write(&path, serde_json::to_vec(&local).unwrap()).unwrap();
            let local_status = std::process::Command::new(local_checker)
                .arg(&path).status().unwrap();
            assert!(local_status.success(), "native source local closure was rejected");
        }

        if let Some(hyper_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_HYPER_CLOSURE_CHECKER")
        {
            let hyper = cb_source_hyper_closure_candidate(&source, &live, &evidence)
                .expect("construct source-bound Hyper candidate");
            std::fs::write(&path, serde_json::to_vec(&hyper).unwrap()).unwrap();
            let hyper_status = std::process::Command::new(hyper_checker)
                .arg(&path).status().unwrap();
            assert!(hyper_status.success(), "native source Hyper closure was rejected");

            let mut forged = hyper;
            let first_term = forged["order"]["ordered_terms"][0].clone();
            forged["order"]["ordered_terms"].as_array_mut().unwrap()
                .push(first_term);
            std::fs::write(&path, serde_json::to_vec(&forged).unwrap()).unwrap();
            let forged_status = std::process::Command::new(
                std::env::var_os("KM_CB_TEST_SOURCE_HYPER_CLOSURE_CHECKER").unwrap())
                .arg(&path).status().unwrap();
            assert!(!forged_status.success(),
                "source Hyper checker accepted a duplicate term universe");
        }

        if let Some(join3_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_JOIN3_CLOSURE_CHECKER")
        {
            let hyper = cb_source_hyper_closure_candidate(&source, &live, &evidence)
                .expect("construct source-bound Join-3 parent candidate");
            let join3 = serde_json::json!({"version": 1, "hyper_closure": hyper});
            std::fs::write(&path, serde_json::to_vec(&join3).unwrap()).unwrap();
            let join3_status = std::process::Command::new(join3_checker)
                .arg(&path).status().unwrap();
            assert!(join3_status.success(), "native source Join-3 closure was rejected");
        }

        if let Some(succ_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_SUCC_CLOSURE_CHECKER")
        {
            let succ = cb_source_succ_closure_candidate(&source, &live, &evidence)
                .expect("construct source-bound Succ candidate");
            std::fs::write(&path, serde_json::to_vec(&succ).unwrap()).unwrap();
            let succ_status = std::process::Command::new(succ_checker)
                .arg(&path).status().unwrap();
            assert!(succ_status.success(), "native source Succ closure was rejected");
        }

        if let Some(eq_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_EQ_CLOSURE_CHECKER")
        {
            let succ = cb_source_succ_closure_candidate(&source, &live, &evidence)
                .expect("construct source-bound Eq parent candidate");
            let eq = serde_json::json!({"version": 1, "succ_closure": succ});
            std::fs::write(&path, serde_json::to_vec(&eq).unwrap()).unwrap();
            let eq_status = std::process::Command::new(eq_checker)
                .arg(&path).status().unwrap();
            assert!(eq_status.success(), "native source Eq closure was rejected");
        }

        if let Some(pred_checker) =
            std::env::var_os("KM_CB_TEST_SOURCE_ORDINARY_PRED_CLOSURE_CHECKER")
        {
            let eq = cb_source_eq_closure_candidate(&source, &live, &evidence)
                .expect("construct source-bound ordinary Pred parent candidate");
            let pred = serde_json::json!({"version": 1, "eq_closure": eq});
            std::fs::write(&path, serde_json::to_vec(&pred).unwrap()).unwrap();
            let pred_status = std::process::Command::new(pred_checker)
                .arg(&path).status().unwrap();
            assert!(pred_status.success(),
                "native source ordinary Pred closure was rejected");
        }

        let mut forged = candidate;
        forged["insertion_evidence"][1]["sender_event"]["event_index"] =
            serde_json::json!(1);
        std::fs::write(&path, serde_json::to_vec(&forged).unwrap()).unwrap();
        let rejected = !std::process::Command::new(&checker)
            .arg(&path).status().unwrap().success();
        let _ = std::fs::remove_file(&path);
        assert!(rejected, "source-bound live checker accepted a forward Pred reference");
    }

    #[test]
    fn pred_standalone_dag_passes_the_real_lean_checker() {
        let Some(checker) =
            std::env::var_os("KM_CB_TEST_STANDALONE_CONTEXT_PROOF_CHECKER")
        else {
            return;
        };
        let predicate = |iri| crate::engine::CbLivePred {
            kind: "concept",
            iri,
            first: crate::calc::X,
            second: None,
        };
        let premise = predicate(0);
        let conclusion = predicate(1);
        let payload = crate::engine::CbLiveClause {
            body: vec![cb_live_pred_literal(&premise)],
            head: vec![cb_live_pred_literal(&conclusion)],
        };
        let provider = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&premise)],
        };
        let result = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![cb_live_pred_literal(&conclusion)],
        };
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.concept_names = vec!["A".to_string(), "B".to_string()];
        live.root_clause_arena = vec![payload.clone(), provider.clone(), result];
        live.contexts[0].root = true;
        live.contexts[1].root = true;
        live.insertion_history = vec![
            crate::engine::CbLiveInsertionEvent {
                sequence: 0,
                context_index: 0,
                root: true,
                clause_id: 0,
                origin_hint: "ontology_fact",
                origin_index: Some(0),
                rule_hint: None,
                rule_evidence: None,
            },
            crate::engine::CbLiveInsertionEvent {
                sequence: 1,
                context_index: 1,
                root: true,
                clause_id: 1,
                origin_hint: "ontology_fact",
                origin_index: Some(1),
                rule_hint: None,
                rule_evidence: None,
            },
            crate::engine::CbLiveInsertionEvent {
                sequence: 2,
                context_index: 1,
                root: true,
                clause_id: 2,
                origin_hint: "derived",
                origin_index: None,
                rule_hint: Some("pred-arrival"),
                rule_evidence: Some(crate::engine::CbLiveRuleEvidence::Pred {
                    sender_context_index: 0,
                    sender_clause_id: 0,
                    edge_label: crate::calc::X,
                    payload: payload.clone(),
                    provider_clause_ids: vec![1],
                    matched_predicates: vec![premise],
                }),
            },
        ];
        let prior = std::collections::HashMap::from([((0, true, 0), 0), ((1, true, 1), 1)]);
        let pred_evidence = cb_pred_event_evidence(&live, &live.insertion_history[2], &prior)
            .expect("exact Pred evidence");
        let wire_ontology = vec![
            cb_wire_clause(&payload, live.comp_ind_bits),
            cb_wire_clause(&provider, live.comp_ind_bits),
        ];
        let source = serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 0,
            "source_clauses": [],
            "role_chains": [],
            "role_axioms": [],
            "ontology": wire_ontology,
        });
        let publication = serde_json::json!({
            "derivation": {
                "production_bound": {
                    "global_model": {"source": source},
                    "live_state": live,
                },
                "insertion_evidence": [
                    {"kind": "seed", "prior_events": [], "trace": [], "discarded": []},
                    {"kind": "seed", "prior_events": [], "trace": [], "discarded": []},
                    pred_evidence,
                ],
            }
        });
        let (document, event_nodes) =
            cb_standalone_context_proof_document(&publication, &[2]).unwrap();
        assert_eq!(event_nodes.len(), 3);
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join(".work/artifacts")
            .join(format!("cb-standalone-pred-{}.json", std::process::id()));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, serde_json::to_vec(&document).unwrap()).unwrap();
        assert!(
            std::process::Command::new(checker)
                .arg(&path)
                .status()
                .unwrap()
                .success(),
            "Lean must accept the native nested Pred DAG"
        );
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn filtered_fact_seed_builds_source_resolution_and_inequality_trace() {
        let concept = |iri| crate::engine::CbLiveLit {
            kind: "concept",
            iri: Some(iri),
            first: crate::calc::X,
            second: None,
        };
        let reflexive = crate::engine::CbLiveLit {
            kind: "inequality",
            iri: None,
            first: crate::calc::X,
            second: Some(crate::calc::X),
        };
        let bottom = crate::engine::CbLiveClause {
            body: vec![concept(0)],
            head: Vec::new(),
        };
        let fact = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![concept(0), concept(1), reflexive],
        };
        let result = crate::engine::CbLiveClause {
            body: Vec::new(),
            head: vec![concept(1)],
        };
        let mut live = live_snapshot();
        live.concept_count = 2;
        live.source_ontology = vec![bottom, fact];
        live.root_clause_arena = vec![result];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 0,
            context_index: 0,
            root: true,
            clause_id: 0,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("filtered-seed"),
            rule_evidence: None,
        };
        let evidence = cb_filtered_seed_event_evidence(&live, &event).unwrap();
        let trace = evidence["trace"].as_array().unwrap();
        assert_eq!(trace.len(), 4);
        assert!(trace[0]["justification"]["premise"].is_object());
        assert!(trace[2]["justification"]["resolve"].is_object());
        assert!(trace[3]["justification"]["deleteReflexiveInequality"].is_object());
    }

    #[test]
    fn filtered_core_bottom_seed_starts_from_exact_core_assumption() {
        let predicate = crate::engine::CbLivePred {
            kind: "concept",
            iri: 0,
            first: crate::calc::X,
            second: None,
        };
        let literal = cb_live_pred_literal(&predicate);
        let mut live = live_snapshot();
        live.contexts[0].core = vec![predicate];
        live.source_ontology = vec![crate::engine::CbLiveClause {
            body: vec![literal],
            head: Vec::new(),
        }];
        live.root_clause_arena = vec![crate::engine::CbLiveClause {
            body: Vec::new(),
            head: Vec::new(),
        }];
        let event = crate::engine::CbLiveInsertionEvent {
            sequence: 0,
            context_index: 0,
            root: true,
            clause_id: 0,
            origin_hint: "derived",
            origin_index: None,
            rule_hint: Some("filtered-seed"),
            rule_evidence: None,
        };
        let evidence = cb_filtered_seed_event_evidence(&live, &event).unwrap();
        let trace = evidence["trace"].as_array().unwrap();
        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0]["justification"]["assumption"], 0);
        assert!(trace[2]["justification"]["resolve"].is_object());
    }
}

// ---------------------------------------------------------------------------
// tableau — the ALC(HOQ) hypertableau (TInput on stdin -> TOutput on stdout)
// ---------------------------------------------------------------------------
pub fn run_tableau() {
    maybe_enable_debug();
    let mut buf = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
        eprintln!("failed to read stdin: {e}");
        exit(1);
    }
    // Run the model build on a large-stack worker thread. The QO/tableau
    // saturation and consistency check recurse proportional to role-chain
    // depth and overflow the default 8 MB main stack on deep ontologies (e.g.
    // transitive-chain composition on ore_ont_14817 — 178 MB RSS yet
    // main-thread stack overflow). KM_TAB_STACK_MB overrides (default 2 GB).
    let stack_mb = std::env::var("KM_TAB_STACK_MB")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(2048);
    let worker = std::thread::Builder::new()
        .stack_size(stack_mb * 1024 * 1024)
        .spawn(move || crate::tableau::run_json(&buf))
        .expect("spawn tableau worker thread");
    match worker.join() {
        Ok(Ok(s)) => {
            let stdout = std::io::stdout();
            let mut h = stdout.lock();
            h.write_all(s.as_bytes()).expect("write stdout");
            h.write_all(b"\n").expect("write newline");
        }
        Ok(Err(e)) => {
            eprintln!("tableau error: {e}");
            exit(1);
        }
        Err(_) => {
            eprintln!("tableau worker thread panicked");
            exit(101);
        }
    }
}
