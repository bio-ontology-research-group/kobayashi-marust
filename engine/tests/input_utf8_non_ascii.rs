//! Regression test for GitHub issue #4: non-ASCII UTF-8 characters in Turtle
//! inputs used to panic horned-owl's OWL functional-syntax writer because it
//! mixed up char counts with byte indices while escaping string literals.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

fn classify_lines(fixture: &str) -> (bool, u64, BTreeSet<String>) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(fixture);
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--lines"])
        .arg(&path)
        .output()
        .expect("run km classify");
    assert!(
        output.status.success(),
        "km classify failed for {}:\nstderr: {}",
        fixture,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8(output.stdout).expect("UTF-8 output");
    let mut consistent = false;
    let mut dropped: u64 = u64::MAX;
    let mut subs = BTreeSet::new();

    for line in stdout.lines() {
        if line.starts_with("CONSISTENT ") {
            consistent = line == "CONSISTENT 1";
        } else if let Some(rest) = line.strip_prefix("DROPPED ") {
            dropped = rest.parse().expect("numeric DROPPED");
        } else if let Some(rest) = line.strip_prefix("SUB\t") {
            subs.insert(rest.to_string());
        }
    }

    (consistent, dropped, subs)
}

#[test]
fn turtle_non_ascii_literal_and_iri_equals_functional() {
    let (c_ttl, d_ttl, subs_ttl) = classify_lines("utf8_non_ascii.ttl");
    let (c_ofn, d_ofn, subs_ofn) = classify_lines("utf8_non_ascii.ofn");

    assert!(c_ttl, "Turtle ontology was inconsistent");
    assert!(c_ofn, "Functional ontology was inconsistent");
    assert_eq!(d_ttl, 0, "Turtle input dropped clauses");
    assert_eq!(d_ofn, 0, "Functional input dropped clauses");
    assert_eq!(
        subs_ttl, subs_ofn,
        "Turtle and functional syntax produced different subsumption sets"
    );
}
