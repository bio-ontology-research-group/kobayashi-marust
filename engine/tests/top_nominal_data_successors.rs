//! `⊤ ⊑ {a}` next to an unqualified data cardinality (m2197 of the
//! nominal+data differential, docs/NOMINALS-CB.md section 6, "Data
//! successors without data values"). Data values are not objects, so one
//! object `a` with two distinct `u`-values is a model of `⊤ ⊑ ≥2 u` and
//! `⊤ ⊑ {a}`. The parser reads the unqualified data filler `rdfs:Literal` as
//! `⊤`, the normaliser shares one definer for both, and before the fix the
//! one-sorted clause set put both `u`-successors under `⊤ ⊑ {a}`, merged them
//! with `a` and with each other, and answered "inconsistent". The two-sorted
//! encoding of `frontend/sorts.rs` was gated on a data value being present;
//! it now also applies when a data property or data range occurs, which
//! fixes the nominal CB route.
//!
//! The native completion bridge (`ht_bridge`, the HT arm of
//! `certified_nominals`, and `auto`) now receives the source data properties
//! (`TInput::data_roles`) and runs its blank-data-node admission gate, which
//! defers on these inputs. A forced route that reads the one-sorted clause
//! stream (`ht_general`) refuses both verdicts (exit 3). The automatic route
//! must answer every input exactly; a forced route may refuse.
//!
//! Expected answers are HermiT 1.4.3.456's. The object probe (`⊤ ⊑ ≥2 r`
//! with `⊤ ⊑ {a}`) stays inconsistent on every route.
use std::collections::BTreeSet;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);

/// `None` is the automatic route.
const ROUTES: [Option<&str>; 5] =
    [None, Some("nominals"), Some("certified_nominals"), Some("ht_general"), Some("ht_bridge")];

type Taxonomy = (bool, BTreeSet<String>, BTreeSet<(String, String)>);

/// Run `km classify --lines` on a fixture. `None` when the route refuses
/// the input (it would have to drop an axiom and fails closed instead).
fn classify(path: &str, route: Option<&str>) -> Option<Taxonomy> {
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
            let mut stderr = String::new();
            child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
            if !status.success() {
                assert!(
                    stderr.contains("unsupported:") && !stdout.contains("CONSISTENT"),
                    "km failed on {path} {route:?}: {stderr}"
                );
                return None;
            }
            let mut consistent = None;
            let mut unsat = BTreeSet::new();
            let mut subs = BTreeSet::new();
            for line in stdout.lines() {
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
            return Some((consistent.expect("CONSISTENT line"), unsat, subs));
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on {path} {route:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/top_nominal_data/{name}", env!("CARGO_MANIFEST_DIR"))
}

/// The `nominals` route gives HermiT's answer.
fn check(name: &str, consistent: bool, unsat: &[&str], subs: &[(&str, &str)]) {
    check_on(&[Some("nominals")], name, consistent, unsat, subs);
}

/// Every route in `routes` that answers gives HermiT's answer; only the
/// forced `ht_general` and `ht_bridge` may refuse the input.
fn check_on(
    routes: &[Option<&str>],
    name: &str,
    consistent: bool,
    unsat: &[&str],
    subs: &[(&str, &str)],
) {
    let path = fixture(name);
    let unsat: BTreeSet<String> = unsat.iter().map(|s| s.to_string()).collect();
    let subs: BTreeSet<(String, String)> =
        subs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
    for &route in routes {
        let Some((got_consistent, got_unsat, got_subs)) = classify(&path, route) else {
            assert!(
                matches!(route, Some("ht_general" | "ht_bridge")),
                "{name}: {route:?} refused the input"
            );
            continue;
        };
        assert_eq!(got_consistent, consistent, "{name} {route:?}: consistency");
        if consistent {
            assert_eq!(got_unsat, unsat, "{name} {route:?}: unsatisfiable classes");
            assert_eq!(got_subs, subs, "{name} {route:?}: subsumptions");
        }
    }
}

/// The generated 12-axiom original: HermiT gives `A ≡ Q2`, `Q1 ⊑ D`.
#[test]
fn m2197_original_is_consistent_with_hermit_taxonomy() {
    check("m2197.ofn", true, &[], &[("A", "Q2"), ("Q2", "A"), ("Q1", "D")]);
}

/// `DisjointClasses(¬(≥2 u), ≤1 u)` (that is `⊤ ⊑ ≥2 u`) and `⊤ ⊑ {a}`.
#[test]
fn m2197_minimal_is_consistent() {
    check("m2197-min.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `⊤ ⊑ {a}`.
#[test]
fn top_min_data_cardinality_with_top_nominal_is_consistent() {
    check("probe_v1.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ∃u.xsd:string`, `⊤ ⊑ {a}`: answered right before the fix.
#[test]
fn top_data_existential_with_top_nominal_is_consistent() {
    check("probe_v2.ofn", true, &[], &[]);
}

/// `A ⊑ ≥2 u`, `A(a)`, `⊤ ⊑ {a}`: every element is `a`, so `A ≡ ⊤`.
#[test]
fn asserted_min_data_cardinality_with_top_nominal_is_consistent() {
    check("probe_v3.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `A(a)` without the nominal axiom.
#[test]
fn top_min_data_cardinality_without_nominal_is_consistent() {
    check("probe_v4.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 r` for an object property `r` with `⊤ ⊑ {a}`: two distinct
/// `r`-successors are objects and must both be `a`. Inconsistent on every
/// route.
#[test]
fn top_min_object_cardinality_with_top_nominal_stays_inconsistent() {
    check_on(&ROUTES, "probe_v5.ofn", false, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `⊤ ⊑ {a, b}`.
#[test]
fn top_min_data_cardinality_with_two_nominals_is_consistent() {
    check("probe_v6.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `⊤ ⊑ ∃r.{a}`, `{a} ⊑ ≤1 r⁻`: the only object is `a`.
#[test]
fn top_min_data_cardinality_with_inverse_functional_hub_is_consistent() {
    check("probe_v7.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `owl:Thing ≡ {a}`.
#[test]
fn top_min_data_cardinality_with_thing_equivalent_nominal_is_consistent() {
    check("probe_v8.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u`, `⊤ ⊑ ∀U.{a}` with the universal role.
#[test]
fn top_min_data_cardinality_with_universal_role_nominal_is_consistent() {
    check("probe_v9.ofn", true, &[], &[]);
}

/// `⊤ ⊑ ≥2 u.xsd:string`, `⊤ ⊑ {a}`: a qualified filler.
#[test]
fn top_qualified_min_data_cardinality_with_top_nominal_is_consistent() {
    check("probe_v10.ofn", true, &[], &[]);
}

/// `⊤ ⊑ =2 u`, `⊤ ⊑ ∃r.{a}`, `⊤ ⊑ ≤1 r`, `{a} ⊑ ≤1 r⁻`, `A ⊑ ≥3 u`:
/// consistent with `A` unsatisfiable.
#[test]
fn exact_data_cardinality_with_has_value_hub_keeps_counting() {
    check("probe_v11.ofn", true, &["A"], &[]);
}

/// Every route gives HermiT's answer; `ht_general` refuses instead, and the
/// automatic route (in `ROUTES`) answers each input.
#[test]
fn hermit_answers_on_every_route() {
    let consistent_empty = [
        "m2197-min.ofn", "probe_v1.ofn", "probe_v2.ofn", "probe_v3.ofn", "probe_v4.ofn",
        "probe_v6.ofn", "probe_v7.ofn", "probe_v8.ofn", "probe_v9.ofn", "probe_v10.ofn",
    ];
    for name in consistent_empty {
        check_on(&ROUTES, name, true, &[], &[]);
    }
    check_on(&ROUTES, "probe_v11.ofn", true, &["A"], &[]);
    check_on(&ROUTES, "m2197.ofn", true, &[], &[("A", "Q2"), ("Q2", "A"), ("Q1", "D")]);
}

/// The forced `ht_general` route reads the one-sorted clause stream: it
/// exits 3 instead of publishing the wrong "inconsistent", and with
/// `KM_ALLOW_APPROXIMATE=1` it marks whatever it publishes.
#[test]
fn forced_one_sorted_route_refuses_both_verdicts() {
    let path = fixture("probe_v1.ofn");
    let run = |allow: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("KM_") {
                command.env_remove(key);
            }
        }
        command.env("KM_ROUTE", "ht_general");
        if allow {
            command.env("KM_ALLOW_APPROXIMATE", "1");
        }
        command.args(["classify", "--lines", &path]).output().unwrap()
    };
    let refused = run(false);
    assert_eq!(refused.status.code(), Some(3));
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(stderr.contains("reads data successors as objects"), "{stderr}");
    let marked = run(true);
    assert!(marked.status.success());
    let stdout = String::from_utf8_lossy(&marked.stdout);
    assert!(stdout.lines().any(|line| line.starts_with("APPROXIMATE\t")), "{stdout}");
}

/// A binary DL-safe rule is not lowered, so the automatic route runs the rule
/// consistency checker over the one-sorted clause stream, which reads the
/// `u`-successors under `⊤ ⊑ {a}` (or `{a, b}` with `≥3 u`) as objects. It
/// used to publish "inconsistent" on all three consistent inputs (HermiT:
/// consistent). The checker's inconsistency is no longer published there;
/// the route answers consistent (with the unapplied rules counted) or fails
/// closed, and never publishes the wrong verdict. The genuine clash
/// (`¬B(a)` with the rule's `B(a)`) must not turn into a consistent answer.
#[test]
fn rule_checker_does_not_publish_a_one_sorted_inconsistency() {
    let run = |name: &str, route: Option<&str>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("KM_") {
                command.env_remove(key);
            }
        }
        if let Some(route) = route {
            command.env("KM_ROUTE", route);
        }
        let output = command.args(["classify", "--lines", &fixture(name)]).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let verdict = stdout.lines().find_map(|line| line.strip_prefix("CONSISTENT ")).map(|v| v == "1");
        (output.status.code(), verdict)
    };
    for route in [None, Some("ht_rules")] {
        for name in ["rule_binary_top_nominal.ofn", "rule_binary_two_nominals.ofn", "rule_binary_nominal_class.ofn"] {
            let (code, verdict) = run(name, route);
            assert!(verdict == Some(true) || (verdict.is_none() && code == Some(3)), "{name} {route:?}: {code:?} {verdict:?}");
        }
        let (code, verdict) = run("rule_binary_clash.ofn", route);
        assert!(verdict == Some(false) || (verdict.is_none() && code == Some(3)), "clash {route:?}: {code:?} {verdict:?}");
    }
}
