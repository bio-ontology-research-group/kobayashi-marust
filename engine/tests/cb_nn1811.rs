//! Reductions of NN-family seed nn1811 (results/agents/2026-11-04/cb-nn1811).
//!
//! - `r19`: `InverseObjectProperties(r s)`, `DisjointClasses(A C)`,
//!   `⊤ ⊑ ≤1 s`, `¬Q4 ⊑ ∃r.∃s.C`. The `r`-successor `y` of an element `x`
//!   has `x` as an `s`-neighbour, so `≤1 s` at `y` merges `y`'s
//!   `s`-successor in `C` into `x`: every `¬Q4` element is in `C`, and
//!   `A ⊑ Q4`.
//! - `r13`: the same with `≤1 r.(∃s.C) ⊑ Q4`, whose complement is
//!   `≥2 r.(∃s.C)`.
//!
//! No axiom mentions an individual. Every CB route answers as HermiT. The
//! native bridge (`ht_bridge`, and through it the automatic route,
//! `production_all` and `certified_nominals`) missed `A ⊑ Q4`: in the `A`
//! probe the `r`-successor is satisfiable-cached from the earlier `C`
//! probe and the generating concept `∃s.C` is absorbed
//! (`is_generating_concept_satisfiable_cached_absorpable`, Konclude cpp
//! 14217), so the successor that merges into the parent is never built.
//! The bridge refuses that absorption for a functional role, but flags a
//! role functional only from the plain clause `s(x,y1) ∧ s(x,y2) → y1≈y2`;
//! the frontend writes `⊤ ⊑ ≤1 s` as an at-most clause guarded by `⊤`
//! definers. The HT view now carries the entailed plain clause
//! (`cb_to_ht::add_entailed_functional_clauses`, docs/ROUTING.md);
//! `KM_HT_NO_ENTAILED_FUNCTIONAL=1` turns that off (negative control).
//!
//! Each `.hermit.json` holds HermiT 1.4's answer, checked by hand in the
//! results README.
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
    fixtures_in("tests/fixtures/cb_nn1811")
}

fn fixtures_in(relative: &str) -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
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
    check_paths(&fixtures(), label, env);
}

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
fn cb_routes_match_hermit() {
    for route in ["nominals", "cb_plain1", "nominal_ni_abox", "certified_card_proxy_abox"] {
        for _ in 0..3 {
            check(route, &with_release(&[("KM_ROUTE", route)]));
        }
    }
}

#[test]
fn bridge_without_the_satisfiable_expander_cache_matches_hermit() {
    check(
        "ht_bridge, KM_HT_NO_SAT_EXP_CACHE",
        &with_release(&[("KM_ROUTE", "ht_bridge"), ("KM_HT_NO_SAT_EXP_CACHE", "1")]),
    );
}

#[test]
fn automatic_route_matches_hermit() {
    for _ in 0..3 {
        check("auto", &with_release(&[]));
    }
}

#[test]
fn bridge_routes_match_hermit() {
    for route in ["ht_bridge", "production_all", "certified_nominals"] {
        for _ in 0..3 {
            check(route, &with_release(&[("KM_ROUTE", route)]));
        }
    }
}

#[test]
fn negative_control_without_the_entailed_functionality_misses_both() {
    let env = with_release(&[("KM_ROUTE", "ht_bridge"), ("KM_HT_NO_ENTAILED_FUNCTIONAL", "1")]);
    for path in fixtures() {
        let got = normalise(&classify(&path, &env));
        assert_ne!(
            got,
            expected(&path),
            "{}: the fixture no longer needs the entailed functionality",
            path.display()
        );
    }
}

/// Family seed fx12 reduced: `Q3 ≡ ≤1 r.(∃s.{b})`, `InverseObjectProperties(s p)`,
/// and an at-most at `b` with a filler (`{b} ⊑ ≤1 p`, whose filler is the
/// frontend's `⊤` definer, or `{b} ⊑ ≤1 p.B`). Every element of `∃s.{b}` is a
/// `p`-successor of `b`, so `⊤ ⊑ Q3`. The automatic route (native bridge)
/// answers as HermiT.
#[test]
fn automatic_route_matches_hermit_on_the_nominal_cb_gap() {
    let paths = fixtures_in("tests/fixtures/cb_nn1811/nominal_cb_gap");
    check_paths(&paths, "auto", &with_release(&[]));
}

/// The nominal CB stack misses `⊤ ⊑ Q3` on both (base too); with the bare
/// clause `p(x,y1) ∧ p(x,y2) → y1≈y2` (`FunctionalObjectProperty(p)`) it
/// is right. Open: results/agents/2026-11-04/cb-nn1811, docs/NOMINALS-CB.md
/// section 12.
#[test]
#[ignore = "nominal CB stack: at-most with a filler at a nominal over inverse-linked predecessors (cb-nn1811, NOMINALS-CB.md section 12)"]
fn nominal_cb_route_matches_hermit_on_the_nominal_cb_gap() {
    let paths = fixtures_in("tests/fixtures/cb_nn1811/nominal_cb_gap");
    check_paths(&paths, "nominals", &with_release(&[("KM_ROUTE", "nominals")]));
}
