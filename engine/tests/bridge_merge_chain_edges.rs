//! Asserted role edges moved through a chain of nominal merges in the
//! native bridge (docs/HYBRID-CB-HT.md section 10, "Asserted edges through
//! merge chains"). Expected answers are HermiT 1.4.3.456's, stored next to
//! each fixture.
//!
//! The five R3 random seeds merge an individual `x` into `y` after an
//! individual named in one of `x`'s role assertions was itself merged into
//! `x` (or into a node merged further), so the assertion's target reaches
//! its live node through two or more merges. The relocation of that
//! assertion used to stop (fail closed, bridge deferred); it now follows the
//! chain to the live node under the folded merge dependency.
use std::collections::BTreeSet;
use std::process::Command;

type Answer = (bool, BTreeSet<String>, BTreeSet<(String, String)>);

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/bridge_merge_chain/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn strip(name: &str) -> String {
    name.trim_start_matches(':').rsplit('#').next().unwrap().to_string()
}

fn classify(path: &str, route: Option<&str>, extra: &[(&str, &str)]) -> Option<Answer> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.args(["classify", "--lines", path]).output().unwrap();
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut consistent = None;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => consistent = Some(single.ends_with(" 1")),
            ["UNSAT", class] => {
                unsat.insert(strip(class));
            }
            ["SUB", sub, sup] => {
                subs.insert((strip(sub), strip(sup)));
            }
            _ => {}
        }
    }
    subs.retain(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b));
    Some((consistent?, unsat, subs))
}

fn hermit(name: &str) -> Answer {
    let text = std::fs::read_to_string(fixture(name)).unwrap();
    let value: serde_json::Value = serde_json::from_str(&text).unwrap();
    let unsat: BTreeSet<String> = value["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| strip(x.as_str().unwrap()))
        .collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (strip(p[0].as_str().unwrap()), strip(p[1].as_str().unwrap())))
        .filter(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b))
        .collect();
    (value["consistent"].as_bool().unwrap(), unsat, subs)
}

const SEEDS: [&str; 5] = ["r1164", "r281", "r947", "r2627", "r2970"];

/// The forced bridge admits all five and must answer each exactly.
#[test]
fn forced_bridge_answers_merge_chains() {
    for seed in SEEDS {
        let got = classify(&fixture(&format!("{seed}.ofn")), Some("ht_bridge"), &[])
            .unwrap_or_else(|| panic!("{seed}: bridge declined"));
        assert_eq!(got, hermit(&format!("{seed}.hermit.json")), "{seed}");
    }
}

#[test]
fn automatic_route_answers_merge_chains() {
    for seed in SEEDS {
        let got = classify(&fixture(&format!("{seed}.ofn")), None, &[])
            .unwrap_or_else(|| panic!("{seed}: no answer"));
        assert_eq!(got, hermit(&format!("{seed}.hermit.json")), "{seed}");
    }
}

/// Each reuse path on its own (class jobs from the representative-cache
/// replay only, or from the retained consistency base only).
#[test]
fn each_reuse_path_answers_merge_chains() {
    for diagnostic in ["KM_BRIDGE_NO_RETAINED_BASE", "KM_BRIDGE_NO_REPRESENTATIVE_CACHE", "KM_BRIDGE_FRESH_ENV"] {
        for seed in SEEDS {
            let got = classify(&fixture(&format!("{seed}.ofn")), Some("ht_bridge"), &[(diagnostic, "1")])
                .unwrap_or_else(|| panic!("{seed} {diagnostic}: bridge declined"));
            assert_eq!(got, hermit(&format!("{seed}.hermit.json")), "{seed} {diagnostic}");
        }
    }
}
