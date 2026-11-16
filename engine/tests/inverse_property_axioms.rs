//! E9: property axioms with `ObjectInverseOf` operands (`SubObjectPropertyOf`
//! on either side or both, `EquivalentObjectProperties`, characteristics of
//! an inverse). km used to refuse them ("named role expected"). Expected
//! rows: HermiT 1.4.3 (consistency, unsatisfiable classes, all named
//! subsumptions and types).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/inverse_property_axioms").join(name)
}

fn rows(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|l| ["CONSISTENT ", "SUB\t", "UNSAT\t", "TYPE\t"].iter().any(|p| l.starts_with(p)))
        .map(str::to_string)
        .collect()
}

#[test]
fn inverse_operands_match_hermit() {
    for case in ["inv1", "inv2", "inv3", "inv4", "inv5", "inv6", "inv7", "inv9", "inv10", "inv11", "inv12"] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars() {
            if key.starts_with("KM_") {
                command.env_remove(key);
            }
        }
        let output = command
            .env("KM_THREADS", "1")
            .args(["classify", "--lines", "--realize"])
            .arg(fixture(&format!("{case}.ofn")))
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        let expected = rows(&std::fs::read_to_string(fixture(&format!("{case}.rows"))).unwrap());
        let got = rows(&stdout);
        if expected.contains("CONSISTENT 0") {
            assert!(got.contains("CONSISTENT 0"), "{case}: {stdout}");
        } else {
            assert_eq!(got, expected, "{case}");
        }
    }
}
