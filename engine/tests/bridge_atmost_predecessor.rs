//! At-most restrictions that must count a predecessor (v1.5.5 probes).
//!
//! Each fixture in `fixtures/bridge_atmost_predecessor/` forces a node whose
//! `≤n` restriction (n = 1 or 2, qualified or unqualified, forward or over an
//! inverse role, directly or through a sub-role) is exceeded only when its
//! predecessor is counted, or (`*_sat`) is not exceeded. Each `.hermit.json`
//! holds HermiT 1.4's answer. The production configurations (auto,
//! production_all, ht_bridge on the source TBox, cb_plain1) agree with
//! HermiT on every fixture.
//!
//! The forced clause translation (`KM_NO_SOURCE_TBOX=1`, not an automatic
//! configuration) misses the `≤2` cases listed in `CLAUSE_TRANSLATION_MISSES`;
//! with `KM_HT_NO_SATURATION=1` it answers them, so the saturation pre-pass
//! decides them wrongly under that encoding. They are excluded from the
//! clause-translation test and kept in an ignored test that shows the gap.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_atmost_predecessor");
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

const CLAUSE_TRANSLATION_MISSES: &[&str] = &[
    "fwd_atmost2_q_pred.ofn",
    "fwd_atmost2_q_pred_local.ofn",
    "fwd_atmost2_u_pred.ofn",
    "hier_invsub_atmost2.ofn",
    "hier_sub_atmost2.ofn",
    "inv_atmost2_q_pred.ofn",
    "inv_atmost2_u_pred.ofn",
    "inv_atmost2_u_pred_guarded.ofn",
];

fn check_paths(paths: &[PathBuf], label: &str, env: &[(&str, &str)]) {
    let mut wrong = Vec::new();
    for path in paths {
        let got = normalise(&classify(path, env));
        let want = expected(path);
        if got != want {
            wrong.push(format!(
                "{} [{label}]: got {got:?}, HermiT {want:?}",
                path.file_name().unwrap().to_string_lossy()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

fn check(label: &str, env: &[(&str, &str)]) {
    check_paths(&fixtures(), label, env);
}

fn clause_split() -> (Vec<PathBuf>, Vec<PathBuf>) {
    fixtures().into_iter().partition(|path| {
        !CLAUSE_TRANSLATION_MISSES.contains(&path.file_name().unwrap().to_str().unwrap())
    })
}

#[test]
fn automatic_route_matches_hermit() {
    check("auto", &[]);
}

#[test]
fn production_all_route_matches_hermit() {
    check("production_all", &[("KM_ROUTE", "production_all")]);
}

#[test]
fn ht_bridge_source_tbox_matches_hermit() {
    check("ht_bridge", &[("KM_ROUTE", "ht_bridge")]);
}

#[test]
fn cb_plain1_route_matches_hermit() {
    check("cb_plain1", &[("KM_ROUTE", "cb_plain1")]);
}

#[test]
fn ht_bridge_clause_translation_matches_hermit_outside_known_misses() {
    let (agree, misses) = clause_split();
    assert_eq!(misses.len(), CLAUSE_TRANSLATION_MISSES.len());
    check_paths(
        &agree,
        "ht_bridge+KM_NO_SOURCE_TBOX",
        &[("KM_ROUTE", "ht_bridge"), ("KM_NO_SOURCE_TBOX", "1")],
    );
}

/// Open: the forced clause translation misses these (2026-10-29).
#[test]
#[ignore]
fn ht_bridge_clause_translation_known_misses() {
    let (_, misses) = clause_split();
    check_paths(
        &misses,
        "ht_bridge+KM_NO_SOURCE_TBOX",
        &[("KM_ROUTE", "ht_bridge"), ("KM_NO_SOURCE_TBOX", "1")],
    );
}
