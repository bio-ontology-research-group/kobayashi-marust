//! Regressions for Konclude's NN-rule in the native bridge
//! (results/agents/2026-11-04/bridge-nn-rule, docs/HYBRID-CB-HT.md
//! section 22).
//!
//! - `f1008`: `≤1 s.(∃p.{c}) ⊑ C` with `InverseFunctional(p)`. Every element
//!   has at most one `s`-successor in `∃p.{c}`, because `c` has at most one
//!   `p`-predecessor, so every class is under `C`. The bridge blocked the
//!   second `s`-successor of a `¬C` element by its sibling, whose
//!   `p`-successor had merged into `c`.
//! - `f439`: `Q2 ≡ {c} ⊓ ≤1 r` with a reflexive `r`, `E ⊑ ∃r⁻.∀r⁻.{c}`,
//!   `InverseFunctional(p)` and `Q5 ≡ ≤1 s⁻.(∃p.E)`. Every `E` element equals
//!   `c` when `c` has one `r`-successor, so `Q2 ⊑ Q5`.
//!
//! - `nn1018min`: `Q1 ≡ ≥3 p⁻.(F ⊓ ∃r.{c})`, `⊤ ⊑ ≤1 r⁻`, `r(b,b)`. `c` has
//!   at most one `r`-predecessor, so `Q1` is unsatisfiable. The ABox
//!   assertion switches the precomputation replay on; the cached nominal `c`
//!   kept its backend blocks below its cached bound, so its at-most (and the
//!   NN-rule) never ran in the class job.
//!
//! All three need the NN-rule: a blockable neighbour of a nominal under an
//! at-most restriction becomes a nominal. With `KM_HT_NO_NN_RULE=1` every
//! fixture fails again (the negative control below).
//!
//! Each `.hermit.json` holds HermiT 1.4's answer, checked by hand in
//! section 22.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_nn_rule");
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

#[test]
fn automatic_route_matches_hermit() {
    for _ in 0..3 {
        check("auto", &with_release(&[]));
    }
}

#[test]
fn forced_bridge_matches_hermit() {
    for _ in 0..3 {
        check("ht_bridge", &with_release(&[("KM_ROUTE", "ht_bridge")]));
    }
}

#[test]
fn negative_control_without_the_nn_rule_misses_both() {
    let env = with_release(&[("KM_ROUTE", "ht_bridge"), ("KM_HT_NO_NN_RULE", "1")]);
    for path in fixtures() {
        let got = normalise(&classify(&path, &env));
        assert_ne!(
            got,
            expected(&path),
            "{}: the fixture no longer needs the NN-rule",
            path.display()
        );
    }
}
