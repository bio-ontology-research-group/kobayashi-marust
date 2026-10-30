//! CB-engine completeness regressions with HermiT answers (v1.5.5).
//!
//! Every fixture in `fixtures/cb_route_completeness/` got an incomplete answer
//! from the consequence-based engine on the automatic route and on the pure CB
//! routes. Each `.hermit.json` holds HermiT 1.4's answer for the matching
//! `.ofn`. The tests run the CB routes without the hypertableau bridge so a
//! regression in the CB engine cannot hide behind another procedure.
//!
//! - `inverse_top_recognition`: `TOP <= D`, `B <= exists t.C`,
//!   `Q3 == exists t.(exists inverse(t).D)`; `B <= Q3` was missed. The
//!   successor of a `B` context needs the parent label `D(y)` to fire the
//!   recognition clause `inv(x,y) & D(y) -> Q(x)`. r-Succ offers a parent's
//!   central labels to its successors, but contexts that attach the shared
//!   facts+TBox closure never entered the closure clauses (here `-> D(x)`)
//!   into their r-Succ pool, so `D(y)` was never offered. See
//!   docs/CB-COMPLETENESS-FIXES.md.
//! - `inverse_forall_top_label`: `TOP <= B`, `exists r.B <= BOTTOM`,
//!   `Q1 == forall inverse(r).A`; every class is below `Q1` because nothing
//!   has an r-successor. The successor needs the parent label `B(y)` from the
//!   shared closure for the same reason (minimised from seed 528).
//! - `seed528`, `seed599` (700-seed ALCHIQ set) and `seed1045`, `seed1189`,
//!   `seed1212` (fresh `gen_alc.py` seeds 1000-1299): the generator seeds that
//!   `cb_plain1` answered wrongly before the fix, all from the same cause
//!   (each one is right with `KM_NO_SHARE=1` on the old binary).
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/cb_route_completeness");
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
fn default1_route_matches_hermit() {
    check("default1", &[("KM_ROUTE", "default1")]);
}

#[test]
fn cb_plain1_route_matches_hermit() {
    check("cb_plain1", &[("KM_ROUTE", "cb_plain1")]);
}

#[test]
fn cb_absorb1_route_matches_hermit() {
    check("cb_absorb1", &[("KM_ROUTE", "cb_absorb1")]);
}

#[test]
fn cb_trigger1_route_matches_hermit() {
    check("cb_trigger1", &[("KM_ROUTE", "cb_trigger1")]);
}

#[test]
fn cb_portfolio16_route_matches_hermit() {
    check("cb_portfolio16", &[("KM_ROUTE", "cb_portfolio16")]);
}

/// The flat closure seeding (`KM_NO_BASE_LAYER`) and the unshared contexts
/// (`KM_NO_SHARE`) must give the same answers as the shared base layer.
#[test]
fn cb_plain1_closure_representations_agree() {
    check("cb_plain1+no_base_layer", &[("KM_ROUTE", "cb_plain1"), ("KM_NO_BASE_LAYER", "1")]);
    check("cb_plain1+no_share", &[("KM_ROUTE", "cb_plain1"), ("KM_NO_SHARE", "1")]);
}
