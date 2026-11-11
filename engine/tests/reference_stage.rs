//! Integration tests for the Lean EL reference stage (`km-el-reference`) in
//! `km classify`.
//!
//! The checker path comes from `KM_EL_TEST_REFERENCE_CHECKER` (or
//! `KM_EL_REFERENCE_CHECKER`); without it the tests skip with a message unless
//! `KM_REQUIRE_LEAN_CHECKERS` is set.
//!
//! Since v1.6.1 the stage prints the `sparse-v1` answer (one row per requested
//! name); the fake-checker tests below feed crafted answers to check that the
//! caller fails closed on a malformed one.

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

/// Drop the SUB rows whose subclass is unsatisfiable: `U SUB X` is entailed
/// for every X, and the production routes print a route-dependent subset.
/// A row with a satisfiable subclass and an unsatisfiable superclass cannot
/// occur and fails the test.
///
/// An inconsistent ontology entails every subsumption: as in the suite digest
/// (`parse_answer_digest`), only the verdict and `dropped` are compared. The
/// production routes list every class as unsatisfiable there, while the
/// reference stage (v1.6.0 and v1.6.1 alike) prints no rows.
fn normalised(v: &serde_json::Value) -> serde_json::Value {
    if v["consistent"] == serde_json::json!(false) {
        return serde_json::json!({
            "consistent": false,
            "subsumptions": [],
            "unsatisfiable": [],
            "dropped": v["dropped"],
        });
    }
    let unsat: std::collections::BTreeSet<String> = v["unsatisfiable"]
        .as_array()
        .map(|a| a.iter().map(|x| x.as_str().unwrap().to_string()).collect())
        .unwrap_or_default();
    let mut subs: Vec<(String, String)> = Vec::new();
    for p in v["subsumptions"].as_array().into_iter().flatten() {
        let (a, b) = (p[0].as_str().unwrap(), p[1].as_str().unwrap());
        if unsat.contains(a) {
            continue;
        }
        assert!(!unsat.contains(b), "anomaly: satisfiable {a} below unsatisfiable {b}");
        subs.push((a.to_string(), b.to_string()));
    }
    subs.sort();
    serde_json::json!({
        "consistent": v["consistent"],
        "subsumptions": subs,
        "unsatisfiable": unsat,
        "dropped": v["dropped"],
    })
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
        normalised(&got),
        normalised(&want),
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

#[test]
fn reference_stage_el_property_and_unsat_matches_unforced() {
    assert_forced_matches_unforced("el_property_unsat.ofn");
}

#[test]
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

#[test]
fn reference_stage_el_tbox_inconsistent_matches_unforced() {
    // The probe pair `probe_a SUB probe_b` carries the inconsistency verdict.
    assert_forced_matches_unforced("el_tbox_inconsistent.ofn");
}

/// A stand-in checker: a POSIX shell script that reads the requested names
/// from the stage input (its last argument) and prints a crafted answer.
fn fake_checker(name: &str, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("reference_stage_fakes");
    std::fs::create_dir_all(&dir).expect("create fake checker dir");
    let path = dir.join(name);
    let script = format!(
        "#!/bin/sh\n\
         for last; do :; done\n\
         named=$(sed -n 's/^{{\"named\":\\(\\[[^]]*\\]\\),\"clauses\".*$/\\1/p' \"$last\")\n\
         list=$(printf '%s' \"$named\" | tr -d '[]' | tr ',' ' ')\n\
         {body}\n"
    );
    std::fs::write(&path, script).expect("write fake checker");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("chmod fake checker");
    path
}

fn assert_fake_declines(checker_path: &Path, expected: &str) {
    let ont = fixture("el_existentials.ofn");
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
        "a malformed reference answer must not publish, stderr:\n{stderr}"
    );
    assert!(forced.stdout.is_empty(), "declined stage must not publish stdout");
    assert!(
        stderr.contains(&format!("KM_REFERENCE_STAGE declined: {expected}")),
        "expected KM_REFERENCE_STAGE declined: {expected} in stderr, got:\n{stderr}"
    );
}

#[test]
fn reference_stage_rows_out_of_order_declines() {
    // Rows in reverse request order: `rows[0].sub` is not `named[0]`.
    let checker_path = fake_checker(
        "rows_reversed.sh",
        "rows=''\n\
         for n in $list; do r=\"{\\\"sub\\\":$n,\\\"unsat\\\":false,\\\"sups\\\":[]}\"; \
         if [ -z \"$rows\" ]; then rows=\"$r\"; else rows=\"$r,$rows\"; fi; done\n\
         printf '{\"format\":\"sparse-v1\",\"named\":%s,\"procedure\":\"el\",\"rows\":[%s]}\\n' \"$named\" \"$rows\"",
    );
    assert_fake_declines(&checker_path, "reference output rows shape mismatch at row 0");
}

#[test]
fn reference_stage_unknown_sup_declines() {
    let checker_path = fake_checker(
        "unknown_sup.sh",
        "rows=''\n\
         for n in $list; do r=\"{\\\"sub\\\":$n,\\\"unsat\\\":false,\\\"sups\\\":[\\\"__km_unknown_sup__\\\"]}\"; \
         if [ -z \"$rows\" ]; then rows=\"$r\"; else rows=\"$rows,$r\"; fi; done\n\
         printf '{\"format\":\"sparse-v1\",\"named\":%s,\"procedure\":\"el\",\"rows\":[%s]}\\n' \"$named\" \"$rows\"",
    );
    assert_fake_declines(
        &checker_path,
        "reference output names an unknown sup: __km_unknown_sup__",
    );
}

#[test]
fn reference_stage_dense_format_declines() {
    // A v1.6.0 dense answer is not accepted any more: fail closed.
    let checker_path = fake_checker(
        "dense_format.sh",
        "printf '{\"cells\":[],\"named\":%s,\"procedure\":\"el\"}\\n' \"$named\"",
    );
    assert_fake_declines(&checker_path, "invalid reference output JSON");
}

#[test]
fn reference_stage_nonzero_exit_reports_stderr_line() {
    // Both streams carry text; the stage's own error is on stderr.
    let checker_path = fake_checker(
        "stderr_first.sh",
        "printf '{\"format\":\"sparse-v1\",\"named\":%s,\"rows\":[\\n' \"$named\"\n\
         echo 'io error: fake stdout failure' >&2\n\
         exit 4",
    );
    assert_fake_declines(&checker_path, "io error: fake stdout failure (checker status:");
}
