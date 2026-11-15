//! W6: data property rows of `km classify --data-properties`. `SUBDATAPROP`,
//! `BOTDATAPROP` and `DATADOMAIN` rows were produced by HermiT 1.4.3
//! (`isEntailed(SubDataPropertyOf)`, satisfiability of `∃p.rdfs:Literal`
//! and of `∃p.rdfs:Literal ⊓ ¬C`); HermiT cannot decide
//! `DisjointDataProperties` (it throws), so the `DISJOINTDATAPROP` rows are
//! checked by hand: `t2` (`xsd:integer` and `xsd:string` ranges), `t3`,
//! `t4` (disjoint enumerations), `t8` (a told disjointness inherited by a
//! sub-property).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/data_properties").join(name)
}

const ROWS: [&str; 5] = ["SUBDATAPROP\t", "BOTDATAPROP\t", "DATADOMAIN\t", "DISJOINTDATAPROP\t", "TOPDATAPROP\t"];

#[test]
fn data_property_rows_match_hermit() {
    for case in ["t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9", "t10", "t12"] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars() {
            if key.starts_with("KM_") {
                command.env_remove(key);
            }
        }
        let output = command
            .env("KM_THREADS", "1")
            .args(["classify", "--lines", "--data-properties"])
            .arg(fixture(&format!("{case}.ofn")))
            .output()
            .unwrap();
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let got: BTreeSet<String> = stdout
            .lines()
            .filter(|l| ROWS.iter().any(|p| l.starts_with(p)))
            .map(str::to_string)
            .collect();
        let expected: BTreeSet<String> = std::fs::read_to_string(fixture(&format!("{case}.rows")))
            .unwrap()
            .lines()
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect();
        assert_eq!(got, expected, "{case}");
        // The probe classes stay internal.
        assert!(!stdout.contains("km.invalid"), "{case}: {stdout}");
    }
}
