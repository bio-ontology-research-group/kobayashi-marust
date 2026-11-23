//! Individual types next to a nominal filler, reduced from campaign cases
//! new_1018_8 and new_1076_68 (v1.7.0 differential campaign, 2026-11-22).
//!
//! The campaign's HermiT 1.4 rows came from `isEntailed(ClassAssertion)` and
//! disagree with HermiT's own consistency test on these inputs, so the
//! expected rows below are checked by hand (and agree with HermiT's
//! consistency of `O ∪ {¬C(a)}`):
//!
//! - `at-most-into-one-of`: `A ⊑ {a1, a2}`, `A ≡ G ⊔ C`, `≤1 s2.C ⊑ A`. If
//!   `a1 ∉ A`, `a1` has two distinct `s2`-successors in `C ⊆ {a1, a2}`, so
//!   `a1 ∈ C ⊆ A`. Hence `A(a1)` and, the same way, `A(a2)`. HermiT's
//!   `isEntailed` misses both.
//! - `existential-into-one-of`: `G ⊑ {a2, a0}`, `¬c0(a3, a2)`, `G(a4)`,
//!   `A(a4)`, `a3 : ∃c0.G`. The successor is `a0`, so `G(a0)`; `a4` may be
//!   `a2`, so `A(a0)` does not follow. HermiT's `isEntailed` claims it.
//!
//! The automatic route must give exactly these rows for the listed
//! individuals or fail closed.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/nominal_oneof_types").join(name)
}

/// The TYPE rows of a realisation, or `None` when the route declines.
fn types(path: &Path) -> Option<Vec<String>> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    for (key, value) in [
        ("KM_THREADS", "1"),
        ("KM_HT_DDB", "1"),
        ("KM_HT_NATIVE_FULL", "1"),
        ("KM_CACHE_CONFORMANCE", "1"),
        ("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1"),
        ("KM_FAST_IRI_GRAMMAR", "1"),
    ] {
        command.env(key, value);
    }
    // The automatic route may run past any test budget on these inputs and
    // fail closed later; a run killed after 120 s counts as silent.
    let mut child = command
        .arg("classify")
        .arg("--lines")
        .arg("--realize")
        .arg(path)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if start.elapsed() > std::time::Duration::from_secs(120) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    };
    let output = child.wait_with_output().unwrap();
    if !status.is_some_and(|status| status.success()) {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.lines().any(|line| line == "CONSISTENT 1"), "{}: {stdout}", path.display());
    Some(stdout.lines().filter(|line| line.starts_with("TYPE\t")).map(str::to_string).collect())
}

fn check(name: &str, individuals: &[&str], want: &[&str]) {
    let Some(rows) = types(&fixture(name)) else { return };
    let got: Vec<&str> = rows
        .iter()
        .map(String::as_str)
        .filter(|row| individuals.iter().any(|ind| row.split('\t').nth(1) == Some(*ind)))
        .collect();
    let mut got = got;
    got.sort();
    let mut want: Vec<&str> = want.to_vec();
    want.sort();
    assert_eq!(got, want, "{name}");
}

#[test]
fn at_most_into_one_of_types_both_individuals() {
    check("at-most-into-one-of.ofn", &[":a1", ":a2"], &["TYPE\t:a1\t:A", "TYPE\t:a2\t:A"]);
}

#[test]
fn existential_into_one_of_does_not_type_the_successor_by_a_neighbour() {
    check(
        "existential-into-one-of.ofn",
        &[":a0", ":a4"],
        &["TYPE\t:a0\t:G", "TYPE\t:a4\t:A", "TYPE\t:a4\t:G"],
    );
}
