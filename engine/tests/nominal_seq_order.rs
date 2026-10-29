//! The plain Sequoia literal ordering is incomplete under nominal
//! clausification (docs/NOMINALS-CB.md section 7): on seed 297 of the bug-1
//! differential generator every nominal route missed `Q1 ⊑ ⊥` while the
//! ordering was auto-selected. Nominal mode now auto-selects the context
//! regime instead (`KM_SEQ_ORDER=context`, docs/PER-CONTEXT-ORDERING.md).
//! Expected answers are HermiT 1.4.3.456's, also derived by hand: the object
//! `a` has a `v`-value, so `a = b` (domain `{b}`), hence `s(b,b)`, and every
//! `Q1 ≡ ¬∃s.{b}` element is `b`.
//!
//! The `p1` fixtures are the cross-individual counterexample of
//! docs/PER-CONTEXT-ORDERING.md section 4. They were missed by the exact
//! (unordered) regime on the `nominals` route: the ground context held
//! `→ B(b) ∨ Q_0(a)` with `B(b)` maximal and never resolved `Q_0(a)`, while the
//! query context announced only `b`.
use std::collections::BTreeSet;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);

fn classify(path: &str, route: Option<&str>) -> (bool, BTreeSet<String>, BTreeSet<(String, String)>) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    let mut child = command
        .args(["classify", "--lines", path])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            let mut stdout = String::new();
            child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
            assert!(status.success(), "km failed on {route:?}");
            let mut consistent = false;
            let mut unsat = BTreeSet::new();
            let mut subs = BTreeSet::new();
            for line in stdout.lines() {
                let fields: Vec<&str> = line.split('\t').collect();
                match fields.as_slice() {
                    [single] if single.starts_with("CONSISTENT ") => consistent = single.ends_with(" 1"),
                    ["UNSAT", class] => {
                        unsat.insert(class.trim_start_matches(':').to_string());
                    }
                    ["SUB", sub, sup] => {
                        subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
                    }
                    _ => {}
                }
            }
            subs.retain(|(a, b)| !unsat.contains(a) && !unsat.contains(b));
            return (consistent, unsat, subs);
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on {route:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

const ROUTES: [Option<&str>; 3] = [None, Some("certified_nominals"), Some("nominals")];

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/nominal_seq_order/{name}", env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn minimal_seed_297_q1_is_unsatisfiable_on_every_nominal_route() {
    let path = fixture("seed297_min.ofn");
    for route in ROUTES {
        let (consistent, unsat, subs) = classify(&path, route);
        assert!(consistent, "{route:?}");
        assert_eq!(unsat, BTreeSet::from(["Q1".to_string()]), "{route:?}");
        assert!(subs.is_empty(), "{route:?}: {subs:?}");
    }
}

#[test]
fn seed_297_q1_is_unsatisfiable_on_every_nominal_route() {
    let path = fixture("seed297.ofn");
    for route in ROUTES {
        let (consistent, unsat, subs) = classify(&path, route);
        assert!(consistent, "{route:?}");
        assert_eq!(unsat, BTreeSet::from(["Q1".to_string()]), "{route:?}");
        assert_eq!(subs, BTreeSet::from([
            ("C".to_string(), "Q3".to_string()), ("Q3".to_string(), "C".to_string())]), "{route:?}");
    }
}

fn classify_with(
    path: &str,
    route: Option<&str>,
    order: Option<&str>,
) -> (bool, BTreeSet<String>, BTreeSet<(String, String)>) {
    match order {
        None => classify(path, route),
        Some(value) => classify_env(path, route, &[("KM_SEQ_ORDER", value)]),
    }
}

fn classify_env(
    path: &str,
    route: Option<&str>,
    extra: &[(&str, &str)],
) -> (bool, BTreeSet<String>, BTreeSet<(String, String)>) {
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
    let output = command
        .args(["classify", "--lines", path])
        .output()
        .unwrap();
    assert!(output.status.success(), "km failed on {route:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut consistent = false;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => consistent = single.ends_with(" 1"),
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
            }
            _ => {}
        }
    }
    subs.retain(|(a, b)| !unsat.contains(a) && !unsat.contains(b));
    (consistent, unsat, subs)
}

#[test]
fn p1_cross_individual_subsumption_on_every_nominal_route() {
    for name in ["p1_cross_individual.ofn", "p1_cross_individual_swapped.ofn"] {
        let path = fixture(name);
        for route in ROUTES {
            let (consistent, unsat, subs) = classify(&path, route);
            assert!(consistent, "{name} {route:?}");
            assert!(unsat.is_empty(), "{name} {route:?}: {unsat:?}");
            assert_eq!(subs, BTreeSet::from([("Q".to_string(), "B".to_string())]), "{name} {route:?}");
        }
    }
}

/// The context regime itself, forced, on the exact CB route: both
/// counterexamples are answered.
#[test]
fn forced_context_regime_answers_both_counterexamples() {
    let (consistent, unsat, subs) = classify_with(&fixture("seed297_min.ofn"), Some("nominals"), Some("context"));
    assert!(consistent);
    assert_eq!(unsat, BTreeSet::from(["Q1".to_string()]));
    assert!(subs.is_empty(), "{subs:?}");
    for name in ["p1_cross_individual.ofn", "p1_cross_individual_swapped.ofn"] {
        let (consistent, unsat, subs) = classify_with(&fixture(name), Some("nominals"), Some("context"));
        assert!(consistent, "{name}");
        assert!(unsat.is_empty(), "{name}: {unsat:?}");
        assert_eq!(subs, BTreeSet::from([("Q".to_string(), "B".to_string())]), "{name}");
    }
}
