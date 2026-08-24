//! Frontend invocation: spawn the `ofn` worker in `--meta` split mode so the
//! (up to ~580 MB) clause set streams straight to a temp file and never enters
//! this process's memory. Port of `owl_classify.run_ofn_split`.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
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
/// Below this ontology-file size, run the frontend IN-PROCESS (call
/// `ofn_to_clauses` directly) instead of forking the `ofn` subprocess. Measured:
/// on trivial onts the subprocess fork/exec + meta round-trip is ~15-25 ms of
/// the ~0.12 s total — the difference between a WIN and a tie against Konclude on
/// the ~125 near-tie onts. Kept SMALL so the frontend's transient parse peak
/// (multi-GB on the giants) stays isolated in the subprocess: at 4 MB the
/// in-process transient peak is only tens of MB and is freed before the engine
/// runs, so the classify RSS high-water-mark is unaffected.
const IN_PROCESS_OFN_MAX: u64 = 4 << 20;
const GIANT_IN_PROCESS_OFN_MIN: u64 = 300 << 20;
const GIANT_IN_PROCESS_OFN_MAX: u64 = 600 << 20;

fn giant_source_uses_certified_rbox(path: &Path) -> std::io::Result<bool> {
    const TOKENS: &[&[u8]] = &[
        b"InverseObjectProperties(",
        b"SymmetricObjectProperty(",
        b"TransitiveObjectProperty(",
    ];
    const CHUNK: usize = 64 << 10;
    const TAIL: u64 = 1 << 20;
    let overlap = TOKENS.iter().map(|token| token.len()).max().unwrap() - 1;
    let mut file = File::open(path)?;
    let len = file.metadata()?.len();
    if len > TAIL {
        file.seek(SeekFrom::End(-(TAIL as i64)))?;
        let mut tail = Vec::with_capacity(TAIL as usize);
        file.read_to_end(&mut tail)?;
        if TOKENS.iter().any(|token| {
            tail.windows(token.len())
                .any(|window| window == *token)
        }) {
            return Ok(true);
        }
        file.seek(SeekFrom::Start(0))?;
    }
    let mut buffer = vec![0; CHUNK + overlap];
    let mut carried = 0;
    loop {
        let read = file.read(&mut buffer[carried..])?;
        let available = carried + read;
        if TOKENS.iter().any(|token| {
            buffer[..available]
                .windows(token.len())
                .any(|window| window == *token)
        }) {
            return Ok(true);
        }
        if read == 0 {
            return Ok(false);
        }
        carried = overlap.min(available);
        buffer.copy_within(available - carried..available, 0);
    }
}

fn use_in_process_ofn(path: &Path, source_bytes: u64) -> bool {
    if let Some(max) = std::env::var("KM_INPROC_OFN_MAX")
        .ok()
        .and_then(|value| value.parse().ok())
    {
        return source_bytes < max;
    }
    if source_bytes < IN_PROCESS_OFN_MAX {
        return true;
    }
    GIANT_IN_PROCESS_OFN_MIN <= source_bytes
        && source_bytes < GIANT_IN_PROCESS_OFN_MAX
        && !giant_source_uses_certified_rbox(path).unwrap_or(true)
}

/// In-process port of the `ofn --meta` subprocess: parse + clausify directly,
/// write the clauses file the engine reads, and return the parsed `Meta`. The
/// clause set is dropped before returning, so no frontend memory is held during
/// the engine run. `ofn_to_clauses` is the SAME function the subprocess calls,
/// so the output is byte-for-byte identical.
fn run_ofn_in_process(
    ont: &Path,
    clauses_path: &Path,
) -> Result<(Meta, Option<crate::json_io::JInput>), OrchestrateError> {
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
    let mut out = crate::json_io::JInput {
        clauses: result.clauses,
        cb_typed_source: None,
        rbox: result.rbox,
        cardinalities: result.cardinalities,
        definers: result.definers,
        source_axioms: result.source_axioms,
        nominal_abox: result.nominal_abox,
        rules: result.rules,
    };
    // Only EL completion can consume this representation directly. Dropping
    // non-EL inputs before returning preserves the old frontend lifetime and
    // avoids making its allocations part of the orchestrator's RSS high-water.
    let selected_route = meta.route.parse::<crate::routing::Route>().ok();
    let cacheable = std::env::var_os("KM_NO_INPROC_ELC").is_none()
        && std::env::var_os("KM_EL_ABOX_CHECK").is_none()
        && meta.el_rbox_safe
        && !meta.profile.positive_el_abox_materializable
        && selected_route.is_some_and(|route| super::use_atomic_inproc_elc(route, &meta.profile));
    // The subprocess JSON path rebuilds an exactly-sized outer clause vector.
    // Match that footprint before retaining frontend-owned clauses across the
    // phase boundary; spare parser growth capacity otherwise survives into EL
    // completion and raises the classify process's high-water mark.
    if cacheable {
        out.clauses.shrink_to_fit();
    }
    // Exact Elc consumes `out` directly. CertifiedElProduction also consumes
    // it directly and recursively reruns this frontend under ProductionAll if
    // its certificate declines, so neither needs an eager serialized copy.
    if !cacheable {
        let f = File::create(clauses_path)?;
        let mut w = std::io::BufWriter::new(f);
        serde_json::to_writer(&mut w, &out)?;
        std::io::Write::flush(&mut w)?;
    }
    let cached = cacheable.then_some(out);
    Ok((meta, cached))
}

pub fn run_ofn_split(cfg: &Config, ont: &Path) -> Result<(TempPath, Meta), OrchestrateError> {
    let (clauses, meta, _cached, _elc_binary) = run_ofn_split_cached(cfg, ont)?;
    Ok((clauses, meta))
}

/// Split frontend output while retaining the already-built typed input for the
/// small in-process path. The serialized file remains authoritative for every
/// subprocess fallback; callers consume the cache only when the selected
/// classifier also runs in this process.
pub fn run_ofn_split_cached(
    cfg: &Config,
    ont: &Path,
) -> Result<
    (
        TempPath,
        Meta,
        Option<crate::json_io::JInput>,
        Option<TempPath>,
    ),
    OrchestrateError,
> {
    let prepared = super::input::prepare(ont)?;
    let ont = prepared.path();
    let clauses = TempPath::new(".clauses.json");

    // In-process fast path for small ontologies (avoids the ofn subprocess).
    // Very large inputs in the measured band also benefit: structured exact-EL
    // leaves can pass their already-built clauses directly to completion, while
    // the two certified-EL controls preserve their isolated completion route.
    // Any failure falls through to the subprocess path below (identical output).
    let small = std::fs::metadata(ont)
        .map(|m| use_in_process_ofn(ont, m.len()))
        .unwrap_or(false);
    if small && std::env::var_os("KM_NO_INPROC_OFN").is_none() {
        match run_ofn_in_process(ont, clauses.path()) {
            Ok((meta, cached)) => return Ok((clauses, meta, cached, None)),
            // OutOfFragment is a real verdict (not a transient failure): surface it
            // exactly as the subprocess exit-3 path does, don't silently retry.
            Err(e @ OrchestrateError::OutOfFragment(_)) => return Err(e),
            Err(_) => { /* fall through to the subprocess path */ }
        }
    }

    let meta = TempPath::new(".meta.json");
    let elc_binary = TempPath::new(".elc.bin");
    let stderr = TempPath::new(".ofn.err");

    let (ofn_prog, ofn_pre) = cfg.ofn_cmd();
    let status = Command::new(&ofn_prog)
        .args(&ofn_pre)
        .arg(ont)
        .arg("--meta")
        .arg(meta.path())
        .arg("--elc-binary")
        .arg(elc_binary.path())
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
    let elc_binary = std::fs::metadata(elc_binary.path())
        .ok()
        .filter(|metadata| metadata.len() > 8)
        .map(|_| elc_binary);
    Ok((clauses, meta_parsed, None, elc_binary))
}

/// Run `ofn` once with `KM_ABSORB` forced on/off, streaming the (full) clause
/// set to a temp file (the engine ignores the extra meta keys). Used by the
/// absorption portfolio to obtain the *plain* clause set. Port of
/// `_ofn_clauses_file`; returns None on any failure.
pub fn run_ofn_plain(cfg: &Config, ont: &Path, absorb: bool) -> Option<TempPath> {
    let prepared = super::input::prepare(ont).ok()?;
    let ont = prepared.path();
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

#[cfg(test)]
mod tests {
    use super::{giant_source_uses_certified_rbox, TempPath};

    #[test]
    fn giant_rbox_scan_detects_tokens_across_chunk_boundaries() {
        let path = TempPath::new(".ofn");
        let token = b"TransitiveObjectProperty(";
        let mut input = vec![b'x'; (64 << 10) - token.len() / 2];
        input.extend_from_slice(token);
        input.extend_from_slice(b"<r>)");
        std::fs::write(path.path(), input).unwrap();
        assert!(giant_source_uses_certified_rbox(path.path()).unwrap());
    }

    #[test]
    fn giant_rbox_scan_accepts_plain_el_source() {
        let path = TempPath::new(".ofn");
        std::fs::write(
            path.path(),
            b"Ontology(SubClassOf(<A> ObjectSomeValuesFrom(<r> <B>)))",
        )
        .unwrap();
        assert!(!giant_source_uses_certified_rbox(path.path()).unwrap());
    }

    #[test]
    fn giant_rbox_scan_checks_tail_then_full_source() {
        let tail_path = TempPath::new(".ofn");
        let mut tail_input = vec![b'x'; (1 << 20) + 4096];
        tail_input.extend_from_slice(b"InverseObjectProperties(<r> <s>)");
        std::fs::write(tail_path.path(), tail_input).unwrap();
        assert!(giant_source_uses_certified_rbox(tail_path.path()).unwrap());

        let prefix_path = TempPath::new(".ofn");
        let mut prefix_input = b"SymmetricObjectProperty(<r>)".to_vec();
        prefix_input.resize((1 << 20) + 4096, b'x');
        std::fs::write(prefix_path.path(), prefix_input).unwrap();
        assert!(giant_source_uses_certified_rbox(prefix_path.path()).unwrap());
    }
}
