//! Konclude-bridge regressions for SELF (docs/HYBRID-CB-HT.md section 20).
//!
//! Every fixture in `fixtures/bridge_self/` has `ObjectHasSelf` or a
//! reflexive role; each `.hermit.json` holds HermiT 1.4's answer.
//!
//! - `ore12128_reduction_expander_cache`: a 23-axiom reduction of
//!   ore_ont_12128. With the satisfiable expander cache installed on a
//!   terminology with a self edge (reflexive `part_of`), the completion-only
//!   schedule published `world_of_Model53` and two other unsatisfiable
//!   classes as satisfiable: the cause of the base's incomplete 12128 answer
//!   (1,567 of 4,716 unsatisfiable classes). `KM-SOUNDNESS-GATE[self-satexp]`.
//! - `self_seed_*`: SELF seed-family members that the port got wrong before
//!   its guards (a self edge counted by an at-most restriction; the
//!   expansion caches across a self edge).
//! - `self_probe_m*`: self edges with functional, qualified at-most,
//!   inverse-functional, asymmetric, inverse-universal and transitive roles.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

fn names(value: &serde_json::Value) -> Vec<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap().trim_start_matches(':').to_string())
        .collect()
}

/// Consistency, the subsumptions between satisfiable distinct classes, and
/// the unsatisfiable classes. An inconsistent answer carries nothing else.
fn normalise(value: &serde_json::Value) -> Answer {
    let consistent = value["consistent"].as_bool().unwrap();
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = names(&value["unsatisfiable"]).into_iter().collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| {
            let pair = names(pair);
            (pair[0].clone(), pair[1].clone())
        })
        .filter(|(sub, sup)| sub != sup && !unsat.contains(sub) && !unsat.contains(sup))
        .collect();
    (true, subs, unsat)
}

fn classify(path: &Path, env: &[(&str, &str)]) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let result = command
        .arg("classify")
        .arg(path)
        .output()
        .expect("run km classification");
    assert!(
        result.status.success(),
        "{}: {}",
        path.display(),
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&result.stdout).unwrap()
}

fn fixtures() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_self");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "ofn"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "missing fixtures in {}", dir.display());
    paths
}

fn expected(path: &Path) -> Answer {
    let gold = path.with_extension("hermit.json");
    normalise(&serde_json::from_str(&std::fs::read_to_string(gold).unwrap()).unwrap())
}

fn check(label: &str, env: &[(&str, &str)]) {
    let mut wrong = Vec::new();
    for path in fixtures() {
        let got = normalise(&classify(&path, env));
        let want = expected(&path);
        if got != want {
            wrong.push(format!(
                "{} [{label}]: got {got:?}, HermiT {want:?}",
                path.file_name().unwrap().to_string_lossy()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}


const RELEASE: [(&str, &str); 5] = [
    ("KM_HT_DDB", "1"),
    ("KM_HT_NATIVE_FULL", "1"),
    ("KM_CACHE_CONFORMANCE", "1"),
    ("KM_FAST_IRI_GRAMMAR", "1"),
    ("KM_THREADS", "1"),
];

fn with_release(extra: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
    RELEASE.iter().copied().chain(extra.iter().copied()).collect()
}

#[test]
fn automatic_route_matches_hermit() {
    check("auto", &with_release(&[]));
}

#[test]
fn ht_bridge_saturation_first_matches_hermit() {
    check("ht_bridge", &with_release(&[("KM_ROUTE", "ht_bridge")]));
}

#[test]
fn ht_bridge_completion_only_matches_hermit() {
    // The schedule the base ran on every SELF terminology.
    check(
        "ht_bridge+KM_HT_NO_SATURATION",
        &with_release(&[("KM_ROUTE", "ht_bridge"), ("KM_HT_NO_SATURATION", "1")]),
    );
}
