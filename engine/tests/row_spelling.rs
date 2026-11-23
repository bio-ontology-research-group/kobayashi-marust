//! Rows spell names as the source does. A functional data property with a
//! facet range and one data assertion send the automatic route through the
//! ground-rule source compiler, whose numeric normalization wrote every IRI
//! in full: km printed `TYPE :a1 http://ex.org/A` and
//! `SUB http://ex.org/A http://ex.org/F` where the source, every other row
//! and HermiT say `:A` and `:F`.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/row_spelling").join(name)
}

fn km(path: &Path, options: &[&str]) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    let output = command.arg("classify").arg("--lines").args(options).arg(path).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn numeric_normalization_keeps_the_source_spelling() {
    let stdout = km(&fixture("numeric-normalized-source.ofn"), &["--realize"]);
    assert!(stdout.lines().any(|line| line == "TYPE\t:a1\t:A"), "{stdout}");
    let stdout = km(&fixture("numeric-normalized-subsumption.ofn"), &[]);
    assert!(stdout.lines().any(|line| line == "SUB\t:A\t:F"), "{stdout}");
    assert!(!stdout.contains("http://ex.org/"), "{stdout}");
}
