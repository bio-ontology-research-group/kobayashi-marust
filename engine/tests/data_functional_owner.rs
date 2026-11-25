//! Two values of a functional data property on one individual (ore_ont_3205
//! through the Protégé plugin, PARITY4). The plugin decides
//! `isEntailed(NegativeDataPropertyAssertion(p b "x"))` as the inconsistency of
//! the ontology plus `p(b, "x")`, with the command below. The data ABox
//! projection wrote the clash as `DifferentIndividuals(b b)`, which the
//! frontend reads as a vacuous set axiom since bfb7be93, so the automatic route
//! answered consistent; it now writes `ClassAssertion(owl:Nothing b)`.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/data_functional_owner").join(name)
}

fn first_line(path: &Path) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    let output = command
        .args(["classify", "--lines", "--lenient", "--unknown-datatypes=free", "--format", "functional"])
        .arg(path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}: {}", path.display(), String::from_utf8_lossy(&output.stderr));
    String::from_utf8_lossy(&output.stdout).lines().next().unwrap_or("").to_string()
}

#[test]
fn a_second_value_of_a_functional_property_is_inconsistent() {
    assert_eq!(first_line(&fixture("two_values.ofn")), "CONSISTENT 0");
}

#[test]
fn one_value_per_individual_stays_consistent() {
    assert_eq!(first_line(&fixture("one_value.ofn")), "CONSISTENT 1");
}
