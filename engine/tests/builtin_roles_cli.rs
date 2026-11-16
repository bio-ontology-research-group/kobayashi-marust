//! Plain classification with `owl:Nothing` as a property domain or range (bug
//! E7) and with `owl:topObjectProperty` outside class restrictions (bug E8).
//!
//! Each `fixtures/builtin_roles/<case>.ofn` has a `<case>.rows` file with the
//! class rows and types that HermiT 1.4.3 reports through the OWL API, in
//! km's spelling (`CONSISTENT`, every entailed `SUB` pair of satisfiable
//! classes, `UNSAT`, every named `TYPE`). Where HermiT misses an entailment the
//! file holds the entailed rows and says so in a `#` line.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &[
    "dom-nothing", "dom-nothing-full", "ran-nothing", "ran-nothing-sub", "dom-nothing-assert",
    "dom-nothing-inv", "ddom-nothing", "u-sub", "u-subinv", "u-sub2", "u-subex", "u-chain",
    "u-chain2", "u-chainsup", "u-eq", "u-eq3", "u-inv", "u-inv2", "u-trans", "u-sym", "u-refl",
    "u-assert", "u-assertr", "u-neg", "u-subsup", "u-dom-nothing", "u-rule", "b-sub", "b-assert",
    "b-chain", "b-eq", "u-key",
];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/builtin_roles").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    command.arg("classify").args(options).arg(path);
    command.output().unwrap()
}

/// The comparable rows: an inconsistent answer is `CONSISTENT 0` alone, and
/// `SUB` rows of unsatisfiable classes and to `owl:Thing` are left out.
fn rows(text: &str) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = text
        .lines()
        .filter(|line| {
            line.starts_with("CONSISTENT ") || line.starts_with("SUB\t") || line.starts_with("UNSAT\t")
                || line.starts_with("TYPE\t")
        })
        .filter(|line| !line.ends_with("\towl:Thing"))
        .map(str::to_string)
        .collect();
    if out.contains("CONSISTENT 0") {
        return BTreeSet::from(["CONSISTENT 0".to_string()]);
    }
    let unsat: BTreeSet<String> =
        out.iter().filter_map(|line| line.strip_prefix("UNSAT\t")).map(str::to_string).collect();
    out.retain(|line| !line.strip_prefix("SUB\t").is_some_and(|rest| unsat.iter().any(|u| rest.starts_with(&format!("{u}\t")))));
    out
}

#[test]
fn builtin_role_shapes_classify_as_hermit() {
    let mut failures = Vec::new();
    for case in CASES {
        let output = km(&fixture(&format!("{case}.ofn")), &["--lines", "--realize"]);
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        let actual = rows(&String::from_utf8(output.stdout).unwrap());
        let expected = rows(&std::fs::read_to_string(fixture(&format!("{case}.rows"))).unwrap());
        if actual != expected {
            failures.push(format!("{case}: km {actual:?}\n  expected {expected:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
