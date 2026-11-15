//! ABox consistency and realization on small knowledge bases (plan part 1b).
//!
//! Regressions: a negative role assertion `¬r(a,c)` was refuted by any
//! `r(a,b)` (the CB worker read the individual `c` like a variable); a `∀`
//! consumer of a transitive role over ground role assertions depended on the
//! order of the assertions; a repeated `SameIndividual` made the native
//! bridge decline and published `DROPPED 1`. Expected rows in
//! `fixtures/abox/*.rows` were produced by HermiT 1.4.3 (consistency and
//! `getTypes`) and are fixed here as oracles.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &[
    "negative-assertion-other-target",
    "negative-assertion-same-target",
    "negative-assertion-chain",
    "negative-assertion-inverse",
    "negative-assertion-inverse-clash",
    "negative-transitive-ab-bc",
    "negative-transitive-bc-ab",
    "transitive-forall-ab-bc",
    "transitive-forall-bc-ab",
    "transitive-forall-nominal-ab-bc",
    "transitive-forall-nominal-bc-ab",
    "same-individual-repeated",
];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/abox").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    command.arg("classify").arg("--lines").args(options).arg(path);
    command.output().unwrap()
}

fn rows(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| line.starts_with("CONSISTENT ") || line.starts_with("TYPE\t"))
        .map(str::to_string)
        .collect()
}

#[test]
fn consistency_and_types_match_hermit() {
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let expected = rows(&std::fs::read_to_string(fixture(&format!("{case}.rows"))).unwrap());
        for options in [&[][..], &["--realize"][..]] {
            let output = km(&source, options);
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{case} {options:?}: {}", String::from_utf8_lossy(&output.stderr));
            assert!(stdout.lines().any(|line| line == "DROPPED 0"), "{case} {options:?}: {stdout}");
            let mut got = rows(&stdout);
            if options.is_empty() {
                got.retain(|row| row.starts_with("CONSISTENT"));
                let consistency: BTreeSet<String> =
                    expected.iter().filter(|row| row.starts_with("CONSISTENT")).cloned().collect();
                assert_eq!(got, consistency, "{case}");
            } else {
                assert_eq!(got, expected, "{case} --realize");
            }
        }
    }
}

/// E19: a functional data property separates `a` from `b`, and a data value
/// is asserted for both individuals; `{a} ⊓ {b}` is unsatisfiable (HermiT).
/// The native bridge answered it satisfiable; such sources are kept off the
/// bridge (`orchestrate::data_source::shared_data_value_hazard`).
#[test]
fn shared_data_values_keep_nominal_intersections_unsatisfiable() {
    for case in ["e19-data-assertions", "e19-data-has-value", "e19-one-shared-value", "e19-swapped-values"] {
        let output = km(&fixture(&format!("{case}.ofn")), &[]);
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        let got: BTreeSet<String> = stdout
            .lines()
            .filter(|line| line.starts_with("CONSISTENT ") || line.starts_with("UNSAT\t") || line.starts_with("SUB\t"))
            .map(str::to_string)
            .collect();
        let expected: BTreeSet<String> = std::fs::read_to_string(fixture(&format!("{case}.classes")))
            .unwrap()
            .lines()
            .map(str::to_string)
            .collect();
        assert_eq!(got, expected, "{case}");
    }
}
