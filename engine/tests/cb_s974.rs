//! Regressions for the two SELF-family answers of results/agents/2026-11-03/cb-s974.
//!
//! - `s974`, `s974_min`: `Q2 ⊑ ≥ 2 r` with `r` reflexive and inverse
//!   functional is unsatisfiable. The CB engine kept the predecessor merge
//!   `x ≈ y` local (it is in `Pr`, arXiv:1805.01396 Definition 2), so the two
//!   successors merged into `x` never met and `Q2` stayed satisfiable.
//! - `s1966`: `C` occurs only in `ObjectPropertyDomain(:t :C)` with a
//!   head-free `t`. The certified elc worker's bridge preprocessing deleted
//!   that clause, `C` lost its node, and the partial answer published `C`
//!   with no superclass although reflexive `r` puts every class under
//!   `Q3 ≡ ∃r.Self`. `KM_ELC_SEQUENTIAL` makes the race outcome deterministic.
//! - `vacuous_domain_top`: the same loss on the forced `elc_cert` route
//!   (`⊤ ⊑ A`, `C` only in the domain of an unused role, `C ⊑ A` lost).
//!
//! Each `.hermit.json` holds HermiT 1.4's answer.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/cb_s974");
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



const RELEASE: [(&str, &str); 6] = [
    ("KM_HT_DDB", "1"),
    ("KM_HT_NATIVE_FULL", "1"),
    ("KM_CACHE_CONFORMANCE", "1"),
    ("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1"),
    ("KM_FAST_IRI_GRAMMAR", "1"),
    ("KM_THREADS", "1"),
];

fn with_release(extra: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
    RELEASE.iter().copied().chain(extra.iter().copied()).collect()
}

fn check_one(name: &str, label: &str, env: &[(&str, &str)]) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/cb_s974");
    let path = dir.join(format!("{name}.ofn"));
    let got = normalise(&classify(&path, env));
    let want = expected(&path);
    assert_eq!(got, want, "{name} [{label}] differs from HermiT");
}

#[test]
fn automatic_route_matches_hermit() {
    // Three runs each: s1966 was wrong in about half of the runs.
    for _ in 0..3 {
        check("auto", &with_release(&[]));
    }
}

#[test]
fn cb_engine_merges_successors_into_the_predecessor() {
    for name in ["s974", "s974_min"] {
        check_one(name, "cb_plain1", &with_release(&[("KM_ROUTE", "cb_plain1")]));
    }
}

#[test]
fn sequential_elc_partial_keeps_a_class_named_only_by_a_vacuous_role() {
    check_one("s1966", "KM_ELC_SEQUENTIAL", &with_release(&[("KM_ELC_SEQUENTIAL", "1")]));
}

#[test]
fn elc_cert_route_keeps_a_class_named_only_by_a_vacuous_role() {
    check_one("vacuous_domain_top", "elc_cert", &with_release(&[("KM_ROUTE", "elc_cert")]));
}

#[test]
fn rules_route_keeps_classes_named_only_by_dropped_ground_clauses() {
    // `A` and `B` occur only in class assertions and a DL-safe rule; the CB
    // taxonomy of the forced `ht_rules` route drops the ground clauses, and
    // without a query for `A` and `B` it published them with no superclass
    // although `⊤ ⊑ G` (the automatic route answers this input exactly).
    // Expected answer by hand: every class is under `G`; the rule never
    // fires (no element is both A and B).
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/cb_s974/rules");
    let path = dir.join("rules_route_top.ofn");
    let env = with_release(&[("KM_ROUTE", "ht_rules")]);
    let got = normalise(&classify(&path, &env));
    let want = normalise(
        &serde_json::from_str(
            &std::fs::read_to_string(dir.join("rules_route_top.expected.json")).unwrap(),
        )
        .unwrap(),
    );
    assert_eq!(got, want);
}
