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

/// `args` are the post-subcommand arguments: `args[0]` = ontology path, optional
/// `args[1] == "--meta"` and `args[2]` = meta-file path. (For the standalone
/// `ofn` binary this is `env::args()[1..]`; for `km ofn` it is `env::args()[2..]`.)
pub fn run_ofn(args: &[String]) {
    use crate::frontend::ofn_to_clauses;
    if args.is_empty() {
        eprintln!("usage: ofn <ontology.ofn> [--meta <meta.json>]");
        exit(2);
    }
    let path = &args[0];
    let meta_path: Option<&str> = match args.get(1).map(String::as_str) {
        Some("--meta") => match args.get(2) {
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
    // The frontend result owns everything needed below. Release the potentially
    // very large source document before serialising the clause array so both do
    // not contribute to the same peak.
    drop(text);
    // Stream JSON to a buffered stdout (the clause array dominates peak memory).
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());

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
    let input: JInput = match serde_json::from_slice(&buf) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("bad input JSON: {}", e);
            exit(1);
        }
    };
    drop(buf);
    if timing {
        eprintln!(
            "KM_ELC_TIMING parse={:.2}s ({} clauses)",
            t1.elapsed().as_secs_f64(),
            input.clauses.len()
        );
    }
    let t2 = Instant::now();
    match elcomplete::classify(input.clauses) {
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
            if let Err(e) = serde_json::to_writer(&mut w, &out) {
                eprintln!("serialise error: {}", e);
                exit(1);
            }
            let _ = w.flush();
            if timing {
                eprintln!(
                    "KM_ELC_TIMING serialise={:.2}s total={:.2}s",
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
    let subsumptions = r
        .take_subsumptions()
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
