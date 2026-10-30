//! Object guard for the native bridge (`frontend/object_guard.rs`,
//! docs/NOMINALS-CB.md, "Object guard for the native bridge"). The fixtures
//! are seeds of the nominal-plus-data differential (`gen_nomdata.py
//! --no-inverse`) on which the bridge deferred at its datatype gate and the
//! nominal CB route ran for more than 60 s. With the guard the automatic
//! route answers them through the bridge; the answers are HermiT 1.4.3.456's.
//!
//! - `m2000_min` (2 axioms) and `m2000`: class axioms that fail at a blank
//!   data node (`≤1 u ⊑ ∃s.{a}`, `(≥1 u ⊔ ≤1 t.A) ⊑ {a}`);
//! - `m2069`: a class assertion with a datatype outside a positive
//!   existential, moved to the nominal inclusion `{a} ⊑ C`;
//! - `m2146`: `DataPropertyDomain(u DataHasValue(u "y"))`, read as
//!   `≥1 u ⊑ ∃u.{"y"}`;
//! - `m2003`-style declared-only classes are covered by `m2146` (`C` is
//!   only declared; without `C ⊑ G` the bridge missed `C ⊑ B`);
use std::collections::BTreeSet;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(60);

type Taxonomy = (bool, BTreeSet<String>, BTreeSet<(String, String)>);

/// `km classify --lines` on a fixture with the given extra environment:
/// the taxonomy (or `None` on a refusal) and the stderr.
fn classify(name: &str, env: &[(&str, &str)]) -> (Option<Taxonomy>, String) {
    let path = format!("{}/tests/fixtures/bridge_object_guard/{name}", env!("CARGO_MANIFEST_DIR"));
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_TIMING", "1");
    for (key, value) in env {
        command.env(key, value);
    }
    let mut child = command
        .args(["classify", "--lines", &path])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            let mut stdout = String::new();
            child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
            let mut stderr = String::new();
            child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
            if !status.success() {
                assert!(
                    stderr.contains("unsupported:") && !stdout.contains("CONSISTENT"),
                    "km failed on {name}: {stderr}"
                );
                return (None, stderr);
            }
            let mut consistent = None;
            let mut unsat = BTreeSet::new();
            let mut subs = BTreeSet::new();
            for line in stdout.lines() {
                assert!(!line.contains("objguard"), "{name}: the guard class leaked: {line}");
                let fields: Vec<&str> = line.split('\t').collect();
                match fields.as_slice() {
                    [single] if single.starts_with("CONSISTENT ") => {
                        consistent = Some(single.ends_with(" 1"))
                    }
                    ["UNSAT", class] => {
                        unsat.insert(class.trim_start_matches(':').to_string());
                    }
                    ["SUB", sub, sup] => {
                        subs.insert((
                            sub.trim_start_matches(':').to_string(),
                            sup.trim_start_matches(':').to_string(),
                        ));
                    }
                    _ => {}
                }
            }
            subs.retain(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b));
            return (Some((consistent.expect("CONSISTENT line"), unsat, subs)), stderr);
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on {name}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// The automatic route answers `name` exactly (HermiT) through the guarded
/// bridge attempt.
fn check_guarded(name: &str, subs: &[(&str, &str)]) {
    let (taxonomy, stderr) = classify(name, &[]);
    let (consistent, unsat, got) = taxonomy.unwrap_or_else(|| panic!("{name}: refused: {stderr}"));
    assert!(consistent, "{name}: consistency");
    assert!(unsat.is_empty(), "{name}: unsatisfiable classes {unsat:?}");
    let want: BTreeSet<(String, String)> =
        subs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
    assert_eq!(got, want, "{name}: subsumptions");
    assert!(
        stderr.contains("bounded bridge-first (object guard) accepted")
            || stderr.contains("bounded bridge-first accepted"),
        "{name}: not answered by the bridge: {stderr}"
    );
}

#[test]
fn blank_failing_axioms_are_guarded_minimal() {
    check_guarded("m2000_min.ofn", &[]);
}

#[test]
fn blank_failing_axioms_are_guarded() {
    check_guarded(
        "m2000.ofn",
        &[("A", "B"), ("A", "Q3"), ("B", "Q3"), ("Q2", "B"), ("Q2", "Q3"), ("Q3", "B")],
    );
}

#[test]
fn datatype_class_assertion_becomes_a_nominal_inclusion() {
    check_guarded("m2069.ofn", &[("C", "Q1"), ("Q1", "C")]);
}

#[test]
fn data_property_domain_with_a_data_value() {
    check_guarded(
        "m2146.ofn",
        &[("A", "B"), ("C", "B"), ("D", "B"), ("D", "Q1"), ("Q1", "B"), ("Q2", "B"), ("Q3", "B")],
    );
}

/// The forced bridge route reads the source without the guard, so its
/// blank-data-node gate still defers on the minimal input: it must refuse,
/// not answer.
#[test]
fn forced_bridge_without_the_guard_still_defers() {
    let (taxonomy, stderr) = classify("m2000_min.ofn", &[("KM_ROUTE", "ht_bridge")]);
    assert!(taxonomy.is_none(), "ht_bridge answered without the guard: {stderr}");
}
