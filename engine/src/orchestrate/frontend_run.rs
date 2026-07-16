//! Frontend invocation: spawn the `ofn` worker in `--meta` split mode so the
//! (up to ~580 MB) clause set streams straight to a temp file and never enters
//! this process's memory. Port of `owl_classify.run_ofn_split`.

use std::collections::BTreeMap;
use std::fs::File;
use std::path::Path;
use std::process::{Command, Stdio};

use super::tmpfile::TempPath;
use super::{Config, OrchestrateError};

/// Side data from `ofn --meta` (everything needed to map engine output back to
/// OWL, minus the clauses). Mirrors `bin/ofn.rs`'s `Meta`.
#[derive(serde::Deserialize)]
pub struct Meta {
    pub iri_map: BTreeMap<String, String>,
    pub named: Vec<String>,
    pub el_rbox_safe: bool,
    #[serde(default)]
    pub abox_inconsistent: bool,
    #[serde(default)]
    pub asserted_classes: Vec<String>,
    #[serde(default)]
    pub profile: crate::frontend::profile::OntologyProfile,
    #[serde(default = "manual_route")]
    pub route: String,
}

fn manual_route() -> String {
    "manual".to_string()
}

/// Returns the clauses temp file (caller owns it; reasoners read it as stdin)
/// and the parsed meta. The meta temp file is unlinked before returning.
/// The clauses temp file the reasoners consume (`{clauses, cardinalities,
/// rules}` — matches `cli::OfnClausesOnly` exactly, the format the `ofn`
/// subprocess writes).
#[derive(serde::Serialize)]
struct ClausesFile {
    clauses: Vec<crate::json_io::JClause>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rbox: Vec<Vec<String>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    cardinalities: Vec<crate::json_io::CardMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    definers: Vec<crate::json_io::DefinerMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    rules: Vec<crate::json_io::JRule>,
}

/// Below this ontology-file size, run the frontend IN-PROCESS (call
/// `ofn_to_clauses` directly) instead of forking the `ofn` subprocess. Measured:
/// on trivial onts the subprocess fork/exec + meta round-trip is ~15-25 ms of
/// the ~0.12 s total — the difference between a WIN and a tie against Konclude on
/// the ~125 near-tie onts. Kept SMALL so the frontend's transient parse peak
/// (multi-GB on the giants) stays isolated in the subprocess: at 2 MB the
/// in-process transient peak is only tens of MB and is freed before the engine
/// runs, so the classify RSS high-water-mark is unaffected.
const IN_PROCESS_OFN_MAX: u64 = 2 << 20;

/// In-process port of the `ofn --meta` subprocess: parse + clausify directly,
/// write the clauses file the engine reads, and return the parsed `Meta`. The
/// clause set is dropped before returning, so no frontend memory is held during
/// the engine run. `ofn_to_clauses` is the SAME function the subprocess calls,
/// so the output is byte-for-byte identical.
fn run_ofn_in_process(ont: &Path, clauses_path: &Path) -> Result<Meta, OrchestrateError> {
    let text = std::fs::read_to_string(ont).map_err(|e| OrchestrateError::Spawn {
        bin: "ofn".into(),
        source: e,
    })?;
    let result = match crate::frontend::ofn_to_clauses(&text) {
        Ok(r) => r,
        Err(e) => return Err(OrchestrateError::OutOfFragment(e.0)),
    };
    let meta = Meta {
        iri_map: result.iri_map,
        named: result.named,
        el_rbox_safe: result.el_rbox_safe,
        abox_inconsistent: result.abox_inconsistent,
        asserted_classes: result.asserted_classes,
        profile: result.profile,
        route: result.route,
    };
    let out = ClausesFile {
        clauses: result.clauses,
        rbox: result.rbox,
        cardinalities: result.cardinalities,
        definers: result.definers,
        source_axioms: result.source_axioms,
        rules: result.rules,
    };
    let f = File::create(clauses_path)?;
    let mut w = std::io::BufWriter::new(f);
    serde_json::to_writer(&mut w, &out)?;
    std::io::Write::flush(&mut w)?;
    Ok(meta)
}

pub fn run_ofn_split(cfg: &Config, ont: &Path) -> Result<(TempPath, Meta), OrchestrateError> {
    let clauses = TempPath::new(".clauses.json");

    // In-process fast path for small ontologies (avoids the ofn subprocess).
    // Any failure falls through to the subprocess path below (identical output).
    let small = std::fs::metadata(ont)
        .map(|m| m.len() < IN_PROCESS_OFN_MAX)
        .unwrap_or(false);
    if small && std::env::var_os("KM_NO_INPROC_OFN").is_none() {
        match run_ofn_in_process(ont, clauses.path()) {
            Ok(meta) => return Ok((clauses, meta)),
            // OutOfFragment is a real verdict (not a transient failure): surface it
            // exactly as the subprocess exit-3 path does, don't silently retry.
            Err(e @ OrchestrateError::OutOfFragment(_)) => return Err(e),
            Err(_) => { /* fall through to the subprocess path */ }
        }
    }

    let meta = TempPath::new(".meta.json");
    let stderr = TempPath::new(".ofn.err");

    let (ofn_prog, ofn_pre) = cfg.ofn_cmd();
    let status = Command::new(&ofn_prog)
        .args(&ofn_pre)
        .arg(ont)
        .arg("--meta")
        .arg(meta.path())
        .stdin(Stdio::null())
        .stdout(File::create(clauses.path())?)
        .stderr(File::create(stderr.path())?)
        .status()
        .map_err(|e| OrchestrateError::Spawn {
            bin: "ofn".into(),
            source: e,
        })?;

    let code = status.code().unwrap_or(-1);
    if code == 3 {
        let msg = std::fs::read_to_string(stderr.path()).unwrap_or_default();
        let msg = msg.trim();
        return Err(OrchestrateError::OutOfFragment(if msg.is_empty() {
            "out of fragment".into()
        } else {
            msg.into()
        }));
    }
    if code != 0 {
        let msg = std::fs::read_to_string(stderr.path()).unwrap_or_default();
        return Err(OrchestrateError::Worker {
            bin: "ofn".into(),
            code,
            stderr: msg,
        });
    }
    // Read the whole meta file and parse with `from_slice`, NOT
    // `from_reader(File)`: serde_json's reader path is unbuffered here and
    // parses a large meta (ore_ont_10073: 21 MB, 473k iri_map entries) ~14 s
    // vs <1 s from a slice — it was the dominant cost of the frontend phase on
    // large ontologies (19 s → 5 s).
    let meta_bytes = std::fs::read(meta.path())?;
    let meta_parsed: Meta = serde_json::from_slice(&meta_bytes)?;
    Ok((clauses, meta_parsed))
}

/// Run `ofn` once with `KM_ABSORB` forced on/off, streaming the (full) clause
/// set to a temp file (the engine ignores the extra meta keys). Used by the
/// absorption portfolio to obtain the *plain* clause set. Port of
/// `_ofn_clauses_file`; returns None on any failure.
pub fn run_ofn_plain(cfg: &Config, ont: &Path, absorb: bool) -> Option<TempPath> {
    let clauses = TempPath::new(".clauses.json");
    let (ofn_prog, ofn_pre) = cfg.ofn_cmd();
    let status = Command::new(&ofn_prog)
        .args(&ofn_pre)
        .arg(ont)
        .stdin(Stdio::null())
        .stdout(File::create(clauses.path()).ok()?)
        .stderr(Stdio::null())
        .env("KM_ABSORB", if absorb { "1" } else { "0" })
        .status()
        .ok()?;
    if status.code() == Some(0) {
        Some(clauses)
    } else {
        None
    }
}
