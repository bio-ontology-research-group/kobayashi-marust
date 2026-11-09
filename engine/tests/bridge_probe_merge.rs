//! Merges that only a class probe triggers, on the native bridge's reuse of
//! the consistency model (docs/HYBRID-CB-HT.md section 18). Expected answers
//! are HermiT 1.4.3's, stored next to each fixture; both the automatic route
//! and the forced `ht_bridge` route must give them.
//!
//! * `m413_min`: `f` functional below `r`, `r o s -> t`, `t` transitive. A
//!   `B` element pulls `B` onto `i3`, whose `f`-successors `i3` and `i0`
//!   merge, which gives `t(i2, i3)` and, through `i3 : forall t-.D`, `B <= D`.
//!   The cardinality criticality test read a role-successor count that was
//!   always 0, and a non-deterministically derived automaton state never
//!   released the neighbour-expansion block (sections 18.1 and 18.2 of the
//!   design note).
//! * `m413_leaf1`: the same with a disjunction on `i2`, so the consistency
//!   completion is non-deterministic and the class jobs run on the retained
//!   consistency leaf (section 16).
//! * `m37`, `m593`: the DDB analysis read a node slot that a branch-epoch pop
//!   had truncated (index out of bounds on the forced bridge, a timeout on the
//!   automatic route). HermiT: `m37` is inconsistent.
//! * `k163_min`: an inverse-functional merge of a probe element with `i4`
//!   through `i5`; the selective neighbour expansion installed only one of
//!   the cached edges between `i5` and `i4`.
//! * `k1414_min`: `i1 : <= 1 s` over three asserted successors and a probe
//!   element; the later alternatives of the at-most merge branch lost the
//!   rule's reapplication.
use std::collections::BTreeSet;
use std::process::Command;

const CASES: &[&str] = &["m413_min", "m413_leaf1", "m37", "m593", "k163_min", "k1414_min"];

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

fn strip(name: &str) -> String {
    name.trim_start_matches(':').rsplit(['/', '#']).next().unwrap().to_string()
}

fn expected(case: &str) -> Answer {
    let path = format!(
        "{}/tests/fixtures/bridge_probe_merge/{case}.expected.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let value: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    if !value["consistent"].as_bool().unwrap() {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = value["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| strip(v.as_str().unwrap()))
        .collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| (strip(pair[0].as_str().unwrap()), strip(pair[1].as_str().unwrap())))
        .filter(|(sub, sup)| !unsat.contains(sub) && !unsat.contains(sup) && sub != sup && sup != "Thing")
        .collect();
    (true, subs, unsat)
}

fn classify(case: &str, route: Option<&str>) -> Answer {
    let path = format!(
        "{}/tests/fixtures/bridge_probe_merge/{case}.ofn",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    let output = command
        .args(["classify", "--lines", &path])
        .env("KM_HT_DDB", "1")
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_CACHE_CONFORMANCE", "1")
        .env("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1")
        .env("KM_FAST_IRI_GRAMMAR", "1")
        .env("KM_THREADS", "1")
        .output()
        .expect("run km classify");
    assert!(
        output.status.success(),
        "{case} {route:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
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
    let consistent = consistent.unwrap_or_else(|| panic!("{case} {route:?}: no CONSISTENT line"));
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let subs = subs
        .into_iter()
        .filter(|(sub, sup)| !unsat.contains(sub) && !unsat.contains(sup) && sub != sup && sup != "Thing")
        .collect();
    (true, subs, unsat)
}

#[test]
fn probe_triggered_merges_match_hermit_on_both_routes() {
    let mut failures = Vec::new();
    for case in CASES {
        let want = expected(case);
        for route in [None, Some("ht_bridge")] {
            let got = classify(case, route);
            if got != want {
                failures.push(format!(
                    "{case} {route:?}: consistent {} vs {}, missing {:?}, extra {:?}",
                    got.0,
                    want.0,
                    want.1.difference(&got.1).collect::<Vec<_>>(),
                    got.1.difference(&want.1).collect::<Vec<_>>()
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
