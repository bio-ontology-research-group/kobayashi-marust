//! End-to-end contract of the DL-safe rule route: the validated consistency
//! precheck short-circuits ONLY on a detected inconsistency, a consistent rule
//! ontology falls through to normal taxonomy classification, and the route
//! provenance is observable (`route=ht_rules` under both the explicit named
//! route and the automatic semantic-fragment gate). The unsat fixture declares
//! inverse roles on purpose: threading the rbox into the precheck conversion
//! once armed the SHOI classification fence, unseated the ABox nominal seeds,
//! and silently turned the 0.17 s inconsistent verdict (ORE 2669/15516) into a
//! long engine run.

use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn fixture(name: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
        .to_string_lossy()
        .into_owned()
}

/// Run `km classify` with a scrubbed KM_* environment and a hard wall-clock
/// bound (a precheck regression manifests as an unbounded engine run, which
/// must fail this suite, not hang it).
fn classify(args: &[&str], ontology: &str) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_km"));
    cmd.arg("classify");
    cmd.args(args);
    cmd.arg(ontology);
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            cmd.env_remove(&key);
        }
    }
    cmd.env("KM_TIMING", "1");
    cmd.stdin(Stdio::null());
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("spawn km classify");
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        match child.try_wait().expect("poll km classify") {
            Some(_) => break,
            None if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("km classify exceeded 120 s — the rules precheck did not short-circuit");
            }
            None => std::thread::sleep(Duration::from_millis(50)),
        }
    }
    child
        .wait_with_output()
        .expect("collect km classify output")
}

fn json_of(out: &Output) -> serde_json::Value {
    assert!(
        out.status.success(),
        "km classify failed: status={:?} stderr={}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice(&out.stdout).expect("classification JSON")
}

#[test]
fn named_rules_route_short_circuits_on_inconsistency() {
    let out = classify(&["--route", "ht_rules"], &fixture("rule_unsat_inverse.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(v["consistent"], false, "stderr: {stderr}");
    assert_eq!(v["subsumptions"].as_array().map(Vec::len), Some(0));
    // provenance: the named route was applied and the PRECHECK decided, not
    // a downstream engine run.
    assert!(stderr.contains("route=ht_rules"), "stderr: {stderr}");
    assert!(
        stderr.contains("rules-consistency done") && stderr.contains("consistent=false"),
        "stderr: {stderr}"
    );
}

#[test]
fn named_rules_route_falls_through_to_taxonomy_when_consistent() {
    let out = classify(&["--route", "ht_rules"], &fixture("rule_consistent.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(v["consistent"], true, "stderr: {stderr}");
    assert!(stderr.contains("route=ht_rules"), "stderr: {stderr}");
    // The consistent verdict must not print a short-circuit line...
    assert!(!stderr.contains("consistent=false"), "stderr: {stderr}");
    // ...and the DL-safe rules (named-individual-only) must not disturb the
    // TBox taxonomy the fall-through computes.
    let subs: Vec<(String, String)> = v["subsumptions"]
        .as_array()
        .expect("subsumption array")
        .iter()
        .map(|p| {
            (
                p[0].as_str().unwrap().to_string(),
                p[1].as_str().unwrap().to_string(),
            )
        })
        .collect();
    for expected in [
        (":Parent", ":Person"),
        (":Person", ":Human"),
        (":Parent", ":Human"),
    ] {
        assert!(
            subs.iter().any(|(a, b)| a == expected.0 && b == expected.1),
            "missing {expected:?} in {subs:?} (stderr: {stderr})"
        );
    }
}

#[test]
fn automatic_route_selects_the_rules_bundle_for_rule_ontologies() {
    let out = classify(&[], &fixture("rule_unsat_inverse.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    // The semantic-fragment gate must route rule-bearing input to ht_rules
    // (KM_ROUTE defaults to auto for `km classify`).
    assert!(stderr.contains("route=ht_rules"), "stderr: {stderr}");
    assert_eq!(v["consistent"], false, "stderr: {stderr}");
}

#[test]
fn same_individual_guard_fires_and_drives_a_clash() {
    // A body `SameAs(x, y)` guard fires ONLY when x and y bind to one individual.
    // Here `SameIndividual(a, b)` merges a and b, so the merged node carries both
    // A (from a) and B (from b); the rule `A(x) ∧ B(y) ∧ SameAs(x,y) → Bad(x)`
    // then fires, and `Bad ⊓ Good` (disjoint, Good asserted on a) clashes.
    let out = classify(&["--route", "ht_rules"], &fixture("rule_same_unsat.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(
        v["consistent"], false,
        "the SameAs-guarded rule must fire on the merged node (stderr: {stderr})"
    );
    assert!(
        stderr.contains("rules-consistency done") && stderr.contains("consistent=false"),
        "stderr: {stderr}"
    );
}

#[test]
fn same_individual_guard_does_not_fire_without_the_merge() {
    // Control: identical ontology WITHOUT `SameIndividual(a, b)`. Now no single
    // node carries both A and B, the guarded rule never fires, and the ontology
    // is consistent — proving the guard is a real condition, not always-on.
    let out = classify(
        &["--route", "ht_rules"],
        &fixture("rule_same_consistent.ofn"),
    );
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(
        v["consistent"], true,
        "without the merge the SameAs guard is false, so no clash (stderr: {stderr})"
    );
    assert!(!stderr.contains("consistent=false"), "stderr: {stderr}");
}
