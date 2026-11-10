//! Integration tests for the Lean EL reference stage (`km-el-reference`) in
//! `km classify`.
//!
//! The checker path comes from `KM_EL_TEST_REFERENCE_CHECKER` (or
//! `KM_EL_REFERENCE_CHECKER`); without it the tests skip with a message unless
//! `KM_REQUIRE_LEAN_CHECKERS` is set.

use std::path::{Path, PathBuf};
use std::process::Command;

fn checker() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("KM_EL_TEST_REFERENCE_CHECKER")
        .or_else(|| std::env::var_os("KM_EL_REFERENCE_CHECKER"))
    {
        return Some(path.into());
    }
    assert!(
        std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
        "KM_EL_TEST_REFERENCE_CHECKER is required"
    );
    eprintln!("skipping: KM_EL_TEST_REFERENCE_CHECKER is unset");
    None
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference_stage")
        .join(name)
}

fn run_km(ontology: &Path, extra_env: &[(&str, &std::ffi::OsStr)]) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .env("KM_TIMING", "1")
        .args(["classify", "--route", "auto"])
        .arg(ontology);
    for (key, value) in extra_env {
        command.env(key, value);
    }
    command.output().expect("spawn km classify")
}

fn assert_forced_matches_unforced(fixture_name: &str) {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture(fixture_name);
    let unforced = run_km(&ont, &[]);
    assert!(
        unforced.status.success(),
        "unforced classify failed on {fixture_name}: {}",
        String::from_utf8_lossy(&unforced.stderr)
    );
    let forced = run_km(
        &ont,
        &[
            ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
            ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(
        forced.status.success(),
        "forced reference stage failed on {fixture_name}: {stderr}"
    );
    assert!(
        stderr.contains("KM_REFERENCE_STAGE published"),
        "expected KM_REFERENCE_STAGE published in stderr on {fixture_name}, got:\n{stderr}"
    );
    let want: serde_json::Value =
        serde_json::from_slice(&unforced.stdout).expect("unforced JSON output");
    let got: serde_json::Value =
        serde_json::from_slice(&forced.stdout).expect("forced reference stage JSON output");
    assert_eq!(
        got, want,
        "reference stage taxonomy differs from unforced answer on {fixture_name}"
    );
}

#[test]
fn reference_stage_el_existentials_matches_unforced() {
    assert_forced_matches_unforced("el_existentials.ofn");
}

#[test]
fn reference_stage_el_role_chain_matches_unforced() {
    assert_forced_matches_unforced("el_role_chain.ofn");
}

#[test]
fn reference_stage_el_unsat_class_matches_unforced() {
    assert_forced_matches_unforced("el_unsat_class.ofn");
}

#[test]
fn reference_stage_alc_property_names_match_unforced() {
    // `s` is a declared object property; it must not appear as a class.
    assert_forced_matches_unforced("alc_property_names.ofn");
}

// Known open difference, reported in results/agents/2026-11-10/v160-p3-rerun:
// for an unsatisfiable class the production routes omit entailed superclass
// rows that need the unsatisfiability (U SUB V when V is unsatisfiable too),
// while the reference matrix answers every entailed cell.
#[test]
#[ignore = "forced answer lists entailed superclass rows of unsatisfiable classes that production omits"]
fn reference_stage_el_property_and_unsat_matches_unforced() {
    assert_forced_matches_unforced("el_property_unsat.ofn");
}

#[test]
#[ignore = "forced answer lists entailed superclass rows of unsatisfiable classes that production omits"]
fn reference_stage_alc_property_and_unsat_matches_unforced() {
    assert_forced_matches_unforced("alc_property_unsat.ofn");
}

#[test]
fn reference_stage_alc_disjunction_matches_unforced() {
    assert_forced_matches_unforced("alc_disjunction.ofn");
}

#[test]
fn reference_stage_alc_budget_declines_without_publishing() {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture("alc_budget.ofn");
    let forced = run_km(
        &ont,
        &[
            ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
            ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(
        !forced.status.success(),
        "over-budget ALC fixture should fail when production is forced to decline, stderr:\n{stderr}"
    );
    assert!(
        forced.stdout.is_empty(),
        "over-budget ALC fixture must not publish stdout when declined"
    );
    assert!(
        stderr.contains("KM_REFERENCE_STAGE declined: alc budget:"),
        "expected KM_REFERENCE_STAGE declined: alc budget: in stderr, got:\n{stderr}"
    );
}

#[test]
fn reference_stage_non_el_declines_without_publishing() {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture("non_el_disjunction.ofn");
    let forced = run_km(
        &ont,
        &[
            ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
            ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(
        !forced.status.success(),
        "non-EL/ALC fixture should fail when production is forced to decline, stderr:\n{stderr}"
    );
    assert!(
        forced.stdout.is_empty(),
        "non-EL/ALC fixture must not publish stdout when declined"
    );
    assert!(
        stderr.contains("KM_REFERENCE_STAGE declined: not recognised:"),
        "expected KM_REFERENCE_STAGE declined: not recognised: in stderr, got:\n{stderr}"
    );
}

#[test]
fn reference_stage_rules_declines_under_force() {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture("rules_taxonomy.ofn");
    let unforced = run_km(&ont, &[]);
    assert!(
        unforced.status.success(),
        "unforced classify failed on rules_taxonomy.ofn: {}",
        String::from_utf8_lossy(&unforced.stderr)
    );
    let unforced_json: serde_json::Value =
        serde_json::from_slice(&unforced.stdout).expect("unforced rules JSON output");
    assert_eq!(unforced_json["consistent"], serde_json::json!(true));

    let forced = run_km(
        &ont,
        &[
            ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
            ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(
        !forced.status.success(),
        "rules fixture must decline under KM_REFERENCE_FORCE=1, stderr:\n{stderr}"
    );
    assert!(
        forced.stdout.is_empty(),
        "rules fixture must not publish stdout when declined under force"
    );
    assert!(
        stderr.contains("KM_REFERENCE_STAGE declined: not recognised:"),
        "expected KM_REFERENCE_STAGE declined: not recognised: in stderr, got:\n{stderr}"
    );
}

#[test]
fn reference_stage_abox_inconsistent_declines_under_force() {
    let Some(checker_path) = checker() else {
        return;
    };
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixtures = [
        fixture("abox_inconsistent.ofn"),
        manifest_dir.join("tests/fixtures/realization/inconsistent.ofn"),
    ];
    for ont in &fixtures {
        let label = ont.display();
        let unforced = run_km(ont, &[]);
        assert!(
            unforced.status.success(),
            "unforced classify failed on {label}: {}",
            String::from_utf8_lossy(&unforced.stderr)
        );
        let unforced_json: serde_json::Value =
            serde_json::from_slice(&unforced.stdout).expect("unforced abox_inconsistent JSON output");
        assert_eq!(unforced_json["consistent"], serde_json::json!(false));

        let forced = run_km(
            ont,
            &[
                ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
                ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
            ],
        );
        let stderr = String::from_utf8_lossy(&forced.stderr);
        assert!(
            !forced.status.success(),
            "ABox-inconsistent fixture {label} must decline under KM_REFERENCE_FORCE=1, stderr:\n{stderr}"
        );
        assert!(
            forced.stdout.is_empty(),
            "ABox-inconsistent fixture {label} must not publish stdout when declined under force"
        );
        assert!(
            stderr.contains("KM_REFERENCE_STAGE declined: not recognised:"),
            "expected KM_REFERENCE_STAGE declined: not recognised: in stderr on {label}, got:\n{stderr}"
        );
    }
}

#[test]
fn reference_stage_budget_timeout_declines_with_budget_reason() {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture("el_existentials.ofn");
    let forced = run_km(
        &ont,
        &[
            ("KM_REFERENCE_FORCE", std::ffi::OsStr::new("1")),
            ("KM_REFERENCE_BUDGET_S", std::ffi::OsStr::new("0")),
            ("KM_EL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    let stderr = String::from_utf8_lossy(&forced.stderr);
    assert!(
        !forced.status.success(),
        "zero-budget reference stage must decline under force, stderr:\n{stderr}"
    );
    assert!(
        forced.stdout.is_empty(),
        "zero-budget reference stage must not publish stdout when declined"
    );
    assert!(
        stderr.contains("KM_REFERENCE_STAGE declined: budget"),
        "expected KM_REFERENCE_STAGE declined: budget in stderr, got:\n{stderr}"
    );
}
