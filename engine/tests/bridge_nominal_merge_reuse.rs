//! Nominal merges in the native bridge's reuse of the consistency model
//! (docs/HYBRID-CB-HT.md section 10). Expected answers are HermiT
//! 1.4.3.456's, stored next to each fixture.
//!
//! * `bridge_merge_min.ofn`: `{b,c} ⊑ {b}` merges `c` into `b`, and
//!   `a : {b,c}` puts `a` at `b` through a disjunction, so `s(b,c)` and
//!   `a : ∀s.A` give `A(b)` and `Q1 ≡ {b}` is subsumed by `A`. The retained
//!   consistency base lost `a`'s pending disjunction (a stale current-node
//!   pointer swallowed the requeue of the fork node), and the representative
//!   cache replayed `c`'s cached labels without the nominal concept of `b`
//!   (positive nominals are not cache values), so the trigger of `{b,c} ⊑ {b}`
//!   on `c` was already present and never derived `b`.
//! * `r3086`: `r` functional, `r(c,c)`, `r(c,a)` merge `a` into `c`; the
//!   existential `a : ∃r.A` reused the functional successor through the
//!   merged-away link to `a` and wrote `A` onto the ghost node.
//! * `r2730`: the same merges as `bridge_merge_min` with more assertions.
//!
//! `r2730.ofn` and `r3086.ofn` repeat a role assertion, which the bridge
//! does not admit; the `-dedup` files drop the repetition (same HermiT
//! answer) so that the forced bridge route answers them.
use std::collections::BTreeSet;
use std::process::Command;

type Answer = (bool, BTreeSet<String>, BTreeSet<(String, String)>);

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/bridge_nominal_merge/{name}", env!("CARGO_MANIFEST_DIR"))
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

const CASES: [(&str, &str); 5] = [
    ("bridge_merge_min.ofn", "bridge_merge_min.hermit.json"),
    ("r2730-dedup.ofn", "r2730.hermit.json"),
    ("r3086-dedup.ofn", "r3086.hermit.json"),
    ("r2730.ofn", "r2730.hermit.json"),
    ("r3086.ofn", "r3086.hermit.json"),
];

#[test]
fn automatic_route_matches_hermit() {
    for (input, gold) in CASES {
        let got = classify(&fixture(input), None, &[]).unwrap_or_else(|| panic!("{input}: no answer"));
        assert_eq!(got, hermit(gold), "{input}");
    }
}

/// The forced bridge must answer the inputs it admits exactly. The two
/// inputs with a repeated role assertion are not admitted; there the forced
/// route fails closed with no answer.
#[test]
fn forced_bridge_matches_hermit() {
    for (input, gold) in CASES {
        match classify(&fixture(input), Some("ht_bridge"), &[]) {
            Some(got) => assert_eq!(got, hermit(gold), "{input}"),
            None => assert!(!input.ends_with("-dedup.ofn") && input != "bridge_merge_min.ofn", "{input}: bridge declined"),
        }
    }
}

/// Each of the two reuse paths on its own: without the retained base the
/// class jobs start from the representative-cache replay, without the cache
/// they start from the retained consistency base. Both answered
/// `bridge_merge_min` incompletely before the fix.
#[test]
fn each_reuse_path_matches_hermit() {
    for diagnostic in ["KM_BRIDGE_NO_RETAINED_BASE", "KM_BRIDGE_NO_REPRESENTATIVE_CACHE"] {
        for (input, gold) in CASES.iter().take(3) {
            let got = classify(&fixture(input), Some("ht_bridge"), &[(diagnostic, "1")])
                .unwrap_or_else(|| panic!("{input} {diagnostic}: no answer"));
            assert_eq!(got, hermit(gold), "{input} {diagnostic}");
        }
    }
}
