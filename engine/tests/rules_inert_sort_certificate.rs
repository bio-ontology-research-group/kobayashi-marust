//! The inert-sort release of the rule-consistency worker input
//! (`orchestrate/inert_sorts.rs`, docs/NOMINALS-CB.md section 6) is checked
//! by the Lean checker `rules-inert-sort-release-check`
//! (`lean/ContextCalculus/RulesInertSortRelease.lean`,
//! `WireInertSortRelease.check_sound`). These tests run `km classify` with
//! `KM_RULES_INERT_CERT` and `KM_RULES_INERT_LEAN_CHECKER`, so a rejected
//! certificate fails the run, and require a non-empty release.
//!
//! The checker path comes from `KM_RULES_TEST_INERT_LEAN_CHECKER`
//! (`lean/run-rules-certification-gate.sh` sets it); without it the tests
//! skip unless `KM_REQUIRE_LEAN_CHECKERS` is set. The ORE test reads
//! `KM_RULES_TEST_ORE_7278` (the path of ore_ont_7278.owl) and skips without
//! it under the same rule.
use std::path::{Path, PathBuf};
use std::process::Command;

fn checker() -> Option<PathBuf> {
    match std::env::var_os("KM_RULES_TEST_INERT_LEAN_CHECKER") {
        Some(path) => Some(path.into()),
        None => {
            assert!(
                std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                "KM_RULES_TEST_INERT_LEAN_CHECKER is required"
            );
            eprintln!("skipping: KM_RULES_TEST_INERT_LEAN_CHECKER is unset");
            None
        }
    }
}

/// Classify `ontology` with the certificate checked, and return the stdout of
/// the checked run, the stdout of a run without the flags, the released
/// concept count and the certificate files.
fn certified_run(ontology: &Path, checker: &Path, tag: &str) -> (String, String, usize, Vec<PathBuf>) {
    let dir = std::env::temp_dir().join(format!("km-rules-inert-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let run = |certified: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("KM_") {
                command.env_remove(key);
            }
        }
        command.env("KM_TIMING", "1").args(["classify", "--lines"]).arg(ontology);
        if certified {
            command.env("KM_RULES_INERT_CERT", &dir).env("KM_RULES_INERT_LEAN_CHECKER", checker);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "km classify failed (certified={certified}): {}",
            String::from_utf8_lossy(&output.stderr)
        );
        (String::from_utf8(output.stdout).unwrap(), String::from_utf8(output.stderr).unwrap())
    };
    let (checked, stderr) = run(true);
    let (plain, _) = run(false);
    let released = stderr
        .lines()
        .find_map(|line| {
            line.strip_prefix("KM_TIMING rules-consistency released ")
                .and_then(|rest| rest.split_whitespace().next())
                .and_then(|n| n.parse().ok())
        })
        .unwrap_or(0);
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
        .collect();
    files.sort();
    (checked, plain, released, files)
}

fn assert_certified(ontology: &Path, tag: &str) {
    let Some(checker) = checker() else { return };
    let (checked, plain, released, files) = certified_run(ontology, &checker, tag);
    assert!(released > 0, "no inert sort was released on {}", ontology.display());
    assert!(!files.is_empty(), "no certificate was written");
    for file in &files {
        let status = kobayashi_marust::lean_checkers::run_document(&checker, file).unwrap().status;
        assert!(status.success(), "Lean rejected {}", file.display());
    }
    assert_eq!(checked, plain, "the certificate flags changed the answer");
    eprintln!("{tag}: {released} released, {} certificate(s) accepted", files.len());
    if std::env::var_os("KM_RULES_TEST_KEEP_CERT").is_none() {
        let _ = std::fs::remove_dir_all(files[0].parent().unwrap());
    }
}

#[test]
fn small_finite_rule_fixture_release_is_lean_checked() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/rules_inert_sorts/fr373.ofn");
    assert_certified(&fixture, "fr373");
}

#[test]
fn ore_ont_7278_release_is_lean_checked() {
    let Some(path) = std::env::var_os("KM_RULES_TEST_ORE_7278") else {
        assert!(
            std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
            "KM_RULES_TEST_ORE_7278 is required"
        );
        eprintln!("skipping: KM_RULES_TEST_ORE_7278 is unset");
        return;
    };
    assert_certified(Path::new(&path), "ore7278");
}
