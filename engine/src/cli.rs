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
        match verify_cb_lean_publication(&r) {
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
) -> Result<std::collections::BTreeMap<String, std::collections::BTreeSet<String>>, String> {
    let global_path = std::env::var_os("KM_CB_GLOBAL_MODEL_CERT")
        .ok_or_else(|| "KM_CB_GLOBAL_MODEL_CERT is required".to_string())?;
    let checker = std::env::var_os("KM_CB_LEAN_CERT_CHECKER")
        .ok_or_else(|| "KM_CB_LEAN_CERT_CHECKER is required".to_string())?;
    let bundle_path = std::env::var_os("KM_CB_CERT_BUNDLE")
        .ok_or_else(|| "KM_CB_CERT_BUNDLE is required".to_string())?;
    let derivation_candidate_path = std::env::var_os("KM_CB_DERIVATION_CANDIDATE");

    let global_bytes = std::fs::read(&global_path).map_err(|error| {
        format!(
            "cannot read global CB certificate {}: {error}",
            std::path::Path::new(&global_path).display()
        )
    })?;
    let global_model: serde_json::Value = serde_json::from_slice(&global_bytes)
        .map_err(|error| format!("cannot parse global CB certificate: {error}"))?;
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
    if status.success() {
        Ok(public_answer)
    } else {
        Err(format!("CB Lean checker rejected the bundle with {status}"))
    }
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

#[cfg(test)]
mod cb_derivation_candidate_tests {
    use super::*;

    fn live_context(context_id: usize) -> crate::engine::CbLiveContextSnapshot {
        crate::engine::CbLiveContextSnapshot {
            context_index: context_id,
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
            version: 5,
            comp_ind_bits: 17,
            concept_count: 1,
            concept_names: vec!["A".to_string()],
            role_count: 0,
            function_count: 0,
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
            contexts: vec![live_context(7), live_context(11)],
        }
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
