//! Konclude-bridge regressions for `≤0` number restrictions (v1.5.5).
//!
//! Every fixture in `fixtures/bridge_atmost_zero/` needs a `≤0 R.C` (or its
//! spelling `¬≥1 R.C`) to reject a predecessor reached over the inverse of
//! `R`. Each `.hermit.json` holds HermiT 1.4's answer.
//!
//! The bridge built `≤0 R.C` as a `CCATMOST` with parameter 0. The ported
//! saturation's critical at-most test counts only the `R`-successors a node
//! links to, so it never saw the predecessor and kept the saturated node
//! sufficient: on `D ⊑ ∃s.⊤`, `⊤ ⊑ ≤0 s⁻.D` the source-TBox bridge
//! published `D` satisfiable (`seed1241` on the automatic route). Konclude's
//! own builder never emits that concept: it builds `≤0 R.C` as `∀R.¬C`. The
//! bridge builder now does the same, and builds `≥1 R.C` as `∃R.C`.
//!
//! - `seed1241`: fresh `gen_alc.py` seed, wrong on auto and production_all.
//! - `inverse_atmost0_top_existential_filler`: seed 1241 minimised.
//! - `inverse_atmost0_top`, `inverse_atmost0_successor_class`,
//!   `unqualified_inverse_atmost0`: the inverse at-most on TOP, on the
//!   successor's class, and unqualified.
//! - `atmost0_top_inverse_predecessor`: a forward `≤0 s.D` whose `D`
//!   neighbour is the predecessor reached by `∃s⁻`.
//! - `negated_atleast1_inverse_top`: the `¬≥1 s⁻.D` spelling.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_atmost_zero");
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
fn ht_bridge_clause_translation_matches_hermit() {
    check(
        "ht_bridge+KM_NO_SOURCE_TBOX",
        &[("KM_ROUTE", "ht_bridge"), ("KM_NO_SOURCE_TBOX", "1")],
    );
}
