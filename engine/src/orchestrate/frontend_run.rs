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
}

/// Returns the clauses temp file (caller owns it; reasoners read it as stdin)
/// and the parsed meta. The meta temp file is unlinked before returning.
pub fn run_ofn_split(cfg: &Config, ont: &Path) -> Result<(TempPath, Meta), OrchestrateError> {
    let clauses = TempPath::new(".clauses.json");
    let meta = TempPath::new(".meta.json");
    let stderr = TempPath::new(".ofn.err");

    let status = Command::new(cfg.ofn_bin())
        .arg(ont)
        .arg("--meta")
        .arg(meta.path())
        .stdin(Stdio::null())
        .stdout(File::create(clauses.path())?)
        .stderr(File::create(stderr.path())?)
        .status()
        .map_err(|e| OrchestrateError::Spawn { bin: "ofn".into(), source: e })?;

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
        return Err(OrchestrateError::Worker { bin: "ofn".into(), code, stderr: msg });
    }
    let meta_parsed: Meta = serde_json::from_reader(File::open(meta.path())?)?;
    Ok((clauses, meta_parsed))
}
