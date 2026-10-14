//! CB nominal calculus: a context tied to an individual by a merge clause
//! `Γ → Δ ∨ x ≈ o` cannot open an r-Succ edge for `o` (side condition (*)),
//! so it must subscribe to the ground context's body-free conclusions about
//! `o` (r-Pred with n = 0). Fuzz case s1737 and variants (`{c} ⊑ A5`,
//! `A1 ⊑ {b}`, `{c} ⊑ A1` gives `c = b` in the ground context and `A1 ⊑ A5`),
//! checked against HermiT on the nominal CB route and on auto.
use std::collections::BTreeSet;
use std::process::Command;

const CASES: &[&str] = &["base", "union", "second", "inverse", "inverse2", "s1737"];

fn short(name: &str) -> String {
    name.rsplit(['/', '#']).next().unwrap_or(name).trim_start_matches(':').to_string()
}

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

fn normalise(value: &serde_json::Value) -> Answer {
    let consistent = value["consistent"].as_bool().unwrap();
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = value["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| short(v.as_str().unwrap()))
        .collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| {
            (
                short(pair[0].as_str().unwrap()),
                short(pair[1].as_str().unwrap()),
            )
        })
        .filter(|(sub, sup)| !unsat.contains(sub) && sub != sup && sup != "Thing")
        .collect();
    (true, subs, unsat)
}

fn classify(path: &str, route: &str) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let result = command
        .args(["classify", path])
        .env("KM_ROUTE", route)
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_HT_DDB", "1")
        .env("KM_CACHE_CONFORMANCE", "1")
        .env("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1")
        .env("KM_FAST_IRI_GRAMMAR", "1")
        .env("KM_THREADS", "1")
        .output()
        .expect("run km classification");
    assert!(
        result.status.success(),
        "{path}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&result.stdout).unwrap()
}

#[test]
fn cb_nominal_merge_abox_cases_match_hermit() {
    let dir = format!(
        "{}/tests/fixtures/cb_nominal_merge",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut failures = Vec::new();
    for case in CASES {
        let expected: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(format!("{dir}/{case}.expected.json")).unwrap(),
        )
        .unwrap();
        let expected = normalise(&expected);
        for route in ["nominals", "auto"] {
        let actual = normalise(&classify(&format!("{dir}/{case}.ofn"), route));
        if expected != actual {
            failures.push(format!(
                "{case}/{route}: missing {:?}, extra {:?}, consistent {} vs {}",
                expected.1.difference(&actual.1).collect::<Vec<_>>(),
                actual.1.difference(&expected.1).collect::<Vec<_>>(),
                actual.0,
                expected.0
            ));
        }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
