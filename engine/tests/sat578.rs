//! Regressions for two blocking defects behind seed sat578
//! (docs/HYBRID-CB-HT.md section 25, results/agents/2026-11-08/sat578-opus).
//!
//! In every fixture a node `y` outside `Q2` carries `≥2 s⁻.(∃s.{c})` (the
//! negation of `Q2 ≡ ≤1 s⁻.(∃s.{c})`) and is a tree successor of the nominal
//! `c`, so `y` satisfies its own `∃s.{c}` through its parent `c`. The two
//! `s⁻`-successors `w₁, w₂` of `y` carry `∃s.{c}` too. The bridge blocked
//! both by `y` before either linked to `c`, so `c` never saw a second
//! `s`-predecessor and its bound `≤1 s⁻.(∃s.{c})` never clashed:
//!
//! - B6 (`u19.rs`, cpp 18731): c-blocking `w` by `w'` redirects the edge
//!   `y → w` to `w'`. For the form `¬(≤n R.C)` Konclude keeps `w` c-blocked
//!   when `w` is in `C`, so two counted successors redirected to one blocker
//!   (here `y` itself) count once and `≥2 s⁻.(∃s.{c})` at `y` breaks.
//! - B4a (`u19.rs`, cpp 18788): a-blocking counted the nominal parent `c` of
//!   the blocker for `w`'s `∃s.{c}`, although unravelling `w` as a copy of
//!   `y` would add an `s`-predecessor of `c` that no rule at `c` counts.
//!   B4a also counted a node merged into `c` as a tree successor (the port
//!   keeps such links as ghosts; Konclude removes them).
//!
//! Fixtures: `sat578` (the seed of the satisfiable-cache family), the
//! reductions `red_both`, `red_q1`, `red_q4`, the five-axiom cores `min_q1`,
//! `min_q1_some`, `min_q1_inter_f`, and `var_inter_f`; and `fx279` from the
//! cb-nn1811 family (`Q2 ≡ ≤2 r.(∃r.{c})` with `⊤ ⊑ ≤2 r⁻`, so `Q2 ≡ ⊤`), the
//! same cause on a HasValue over a nominal. Each `.hermit.json` holds HermiT
//! 1.4's answer, checked by hand in section 25.1.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sat578");
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
fn forced_bridge_without_saturation_or_caches_matches_hermit() {
    check(
        "ht_bridge+no_sat_no_cache",
        &with_release(&[
            ("KM_ROUTE", "ht_bridge"),
            ("KM_HT_NO_SATURATION", "1"),
            ("KM_HT_NO_SAT_EXP_CACHE", "1"),
            ("KM_BRIDGE_NO_LEAF_REUSE", "1"),
            ("KM_BRIDGE_NO_PRECOMPUTATION_REPLAY", "1"),
        ]),
    );
}

/// With the fix off (`KM_HT_NO_SAT578_FIX=1`: Konclude's B6 and B4a), every
/// fixture is wrong again, as on 274faa6a.
#[test]
fn negative_control_without_the_fix_misses_every_fixture() {
    misses_every_fixture("KM_HT_NO_SAT578_FIX");
}

/// The B6 count test and the B4a nominal guard are each needed: with either
/// one off, every sat578 fixture (all but `fx279`) is wrong (with B4a alone `w` stays c-blocked, with
/// B6 alone it is a-blocked through the nominal `c`).
#[test]
fn negative_control_each_part_is_needed() {
    misses_every_fixture("KM_HT_NO_B6_COLLISION_GUARD");
    misses_every_fixture("KM_HT_NO_B4A_NOMINAL_GUARD");
}

fn misses_every_fixture(switch: &'static str) {
    let env = with_release(&[("KM_ROUTE", "ht_bridge"), (switch, "1")]);
    for path in fixtures().into_iter().filter(|path| !path.ends_with("fx279.ofn")) {
        let got = normalise(&classify(&path, &env));
        assert_ne!(
            got,
            expected(&path),
            "{} with {switch}: the fixture no longer needs this part of the fix",
            path.display()
        );
    }
}
