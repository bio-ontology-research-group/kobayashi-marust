//! The saturation merges all successors of a functional role into one node by
//! extending a copy base with the labels of the other successors. The
//! extension map holds one polarity per concept, so two successors with `B, ¬C`
//! and `¬B, C` (neither polarity in the base) lost the clash: with
//! `A ⊑ ∃s.B ⊓ ∃s.C ⊓ ∃r.A`, `B ⊓ C ⊑ ⊥`, `s ⊑ r` and `r` functional, the
//! base `A` was extended with `¬B, C` only and the native bridge reported `A`
//! satisfiable (HermiT: unsatisfiable). The automatic route used that answer
//! for `--realize --different`.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/bridge_functional_merge")
        .join(name)
}

fn unsat_rows(path: &Path, options: &[&str], env: &[(&str, &str)]) -> Vec<String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.arg("classify").arg("--lines").args(options).arg(path).output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(output.status.success(), "{}: {}", path.display(), String::from_utf8_lossy(&output.stderr));
    assert!(stdout.lines().any(|line| line == "CONSISTENT 1"), "{stdout}");
    let mut rows: Vec<String> =
        stdout.lines().filter(|line| line.starts_with("UNSAT\t")).map(str::to_string).collect();
    rows.sort();
    rows
}

#[test]
fn functional_merge_of_opposite_polarities_stays_unsatisfiable() {
    let path = fixture("opposite-polarity.ofn");
    assert_eq!(unsat_rows(&path, &[], &[("KM_ROUTE", "ht_bridge")]), ["UNSAT\t:A"]);
    assert_eq!(unsat_rows(&path, &[], &[]), ["UNSAT\t:A"]);
}

#[test]
fn realization_with_different_rows_keeps_unsatisfiable_classes() {
    // A fuzz case whose realization route answers from the native bridge.
    let path = fixture("fuzz-v303-10.ofn");
    let expected = ["UNSAT\t:A", "UNSAT\t:E"];
    assert_eq!(unsat_rows(&path, &[], &[("KM_ROUTE", "ht_bridge")]), expected);
    assert_eq!(unsat_rows(&path, &["--realize", "--different"], &[]), expected);
    assert_eq!(unsat_rows(&path, &["--realize"], &[]), expected);
}
