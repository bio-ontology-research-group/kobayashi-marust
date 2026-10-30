//! Rule-route answers checked by the Lean checker `rules-cert-check`
//! (`lean/ContextCalculus/RulesRouteCertificate.lean`,
//! `WireRulesCertificate.check_sound`). Each test runs `km classify` with
//! `KM_RULES_LEAN_CERT` and `KM_RULES_LEAN_CHECKER`, so a rejected or missing
//! certificate fails the run; it then requires at least one certificate, runs
//! the checker on each again, and compares the answer with an unflagged run.
//!
//! The checker path comes from `KM_RULES_TEST_LEAN_CHECKER`
//! (`lean/run-rules-certification-gate.sh` sets it); without it the tests
//! skip unless `KM_REQUIRE_LEAN_CHECKERS` is set. The ORE test reads
//! `KM_RULES_TEST_ORE_7278`.
use std::path::{Path, PathBuf};
use std::process::Command;

fn checker() -> Option<PathBuf> {
    match std::env::var_os("KM_RULES_TEST_LEAN_CHECKER") {
        Some(path) => Some(path.into()),
        None => {
            assert!(
                std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                "KM_RULES_TEST_LEAN_CHECKER is required"
            );
            eprintln!("skipping: KM_RULES_TEST_LEAN_CHECKER is unset");
            None
        }
    }
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn km(ontology: &Path, route: Option<&str>, env: &[(&str, &std::ffi::OsStr)]) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_TIMING", "1").args(["classify", "--lines"]);
    if let Some(route) = route {
        command.args(["--route", route]);
    }
    command.arg(ontology);
    for (key, value) in env {
        command.env(key, value);
    }
    command.output().unwrap()
}

/// The forced rule route (`--route ht_rules`) sends a fixture to the rule
/// worker that the automatic route would answer by ground-rule expansion.
/// Run certified and plain; return the certificate files and stderr.
fn assert_certified(ontology: &Path, tag: &str, route: Option<&str>) -> (Vec<PathBuf>, String) {
    let Some(checker) = checker() else { return (Vec::new(), String::new()) };
    let dir = std::env::temp_dir().join(format!("km-rules-lean-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let checked = km(ontology, route, &[
        ("KM_RULES_LEAN_CERT", dir.as_os_str()),
        ("KM_RULES_LEAN_CHECKER", checker.as_os_str()),
    ]);
    let stderr = String::from_utf8_lossy(&checked.stderr).to_string();
    assert!(checked.status.success(), "certified km classify failed on {tag}: {stderr}");
    let plain = km(ontology, route, &[]);
    assert!(plain.status.success(), "plain km classify failed on {tag}");
    assert_eq!(checked.stdout, plain.stdout, "the certificate flags changed the answer on {tag}");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no rule-route certificate was written for {tag}");
    for file in &files {
        let out = Command::new(&checker).arg(file).output().unwrap();
        assert!(out.status.success(), "Lean rejected {}", file.display());
        eprintln!("{tag}: {}", String::from_utf8_lossy(&out.stdout).trim());
    }
    for line in stderr.lines().filter(|l| l.contains("rules-lean-cert")) {
        eprintln!("{tag}: {line}");
    }
    (files, stderr)
}

fn cleanup(files: &[PathBuf]) {
    if std::env::var_os("KM_RULES_TEST_KEEP_CERT").is_none() {
        if let Some(dir) = files.first().and_then(|f| f.parent()) {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}

#[test]
fn consistent_rule_fixture_has_a_checked_model() {
    let (files, _) = assert_certified(&fixture("rule_consistent.ofn"), "rule_consistent", Some("ht_rules"));
    cleanup(&files);
}

#[test]
fn inconsistent_rule_fixture_has_a_checked_refutation() {
    let (files, _) = assert_certified(&fixture("rule_same_unsat.ofn"), "rule_same_unsat", Some("ht_rules"));
    cleanup(&files);
}

#[test]
fn inverse_rule_refutation_is_checked() {
    let (files, _) = assert_certified(&fixture("rule_unsat_inverse.ofn"), "rule_unsat_inverse", Some("ht_rules"));
    cleanup(&files);
}

#[test]
fn finite_rule_inert_sort_fixture_is_checked() {
    let (files, _) = assert_certified(&fixture("rules_inert_sorts/fr373.ofn"), "fr373", None);
    cleanup(&files);
}

/// A certificate edited to claim the opposite verdict is rejected.
#[test]
fn forged_rule_certificate_is_rejected() {
    let Some(checker) = checker() else { return };
    let (files, _) = assert_certified(&fixture("rule_consistent.ofn"), "forged", Some("ht_rules"));
    let text = std::fs::read_to_string(&files[0]).unwrap();
    let forged = text.replacen("\"consistent\":true", "\"consistent\":false", 1);
    assert_ne!(forged, text, "the fixture certificate has no consistent verdict");
    let path = files[0].with_file_name("forged.json");
    std::fs::write(&path, forged).unwrap();
    let out = Command::new(&checker).arg(&path).output().unwrap();
    assert!(!out.status.success(), "a forged rule-route certificate was accepted");
    cleanup(&files);
}

#[test]
fn ore_ont_7278_rule_verdict_is_checked() {
    let Some(path) = std::env::var_os("KM_RULES_TEST_ORE_7278") else {
        assert!(
            std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
            "KM_RULES_TEST_ORE_7278 is required"
        );
        eprintln!("skipping: KM_RULES_TEST_ORE_7278 is unset");
        return;
    };
    let (files, _) = assert_certified(Path::new(&path), "ore7278", None);
    cleanup(&files);
}
