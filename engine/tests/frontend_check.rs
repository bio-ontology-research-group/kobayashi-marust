//! Integration tests for `KM_FRONTEND_CHECK=1` in `km classify`: the final
//! answer is compared with the Lean OWL reference procedure
//! (`km-owl-reference`, `lean/KMOWLReferenceCheck.lean`).
//!
//! The real checker comes from `KM_OWL_TEST_REFERENCE_CHECKER` (or
//! `KM_OWL_REFERENCE_CHECKER`); without it those tests skip with a message
//! unless `KM_REQUIRE_LEAN_CHECKERS` is set. The fake-checker tests (a POSIX
//! shell script printing a crafted answer, as in `reference_stage.rs`) need
//! no Lean build and always run.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

fn checker() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("KM_OWL_TEST_REFERENCE_CHECKER")
        .or_else(|| std::env::var_os("KM_OWL_REFERENCE_CHECKER"))
    {
        return Some(path.into());
    }
    assert!(
        std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
        "KM_OWL_TEST_REFERENCE_CHECKER is required"
    );
    eprintln!("skipping: KM_OWL_TEST_REFERENCE_CHECKER is unset");
    None
}

fn fixture(name: &str) -> PathBuf {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let own = base.join("frontend_check").join(name);
    if own.is_file() {
        own
    } else {
        base.join("reference_stage").join(name)
    }
}

/// `km classify [--lines]` with every caller `KM_*` variable removed.
fn run_km(ontology: &Path, lines: bool, extra_env: &[(&str, &OsStr)]) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .env("KM_TIMING", "1")
        .env("KM_THREADS", "1")
        .args(["classify", "--route", "auto"]);
    if lines {
        command.arg("--lines");
    }
    command.arg(ontology);
    for (key, value) in extra_env {
        command.env(key, value);
    }
    command.output().expect("spawn km classify")
}

fn check_env(checker: &Path) -> Vec<(&'static str, &OsStr)> {
    vec![
        ("KM_FRONTEND_CHECK", OsStr::new("1")),
        ("KM_OWL_REFERENCE_CHECKER", checker.as_os_str()),
    ]
}

/// The check agrees, names the procedure and leaves the output unchanged, in
/// both output modes.
fn assert_agrees(fixture_name: &str, procedure: &str) {
    let Some(checker_path) = checker() else {
        return;
    };
    let ont = fixture(fixture_name);
    for lines in [true, false] {
        let off = run_km(&ont, lines, &[]);
        assert!(
            off.status.success(),
            "classify failed on {fixture_name}: {}",
            String::from_utf8_lossy(&off.stderr)
        );
        let off_stderr = String::from_utf8_lossy(&off.stderr);
        assert!(
            !off_stderr.contains("KM_FRONTEND_CHECK"),
            "the check ran while off on {fixture_name}:\n{off_stderr}"
        );
        let on = run_km(&ont, lines, &check_env(&checker_path));
        let stderr = String::from_utf8_lossy(&on.stderr);
        assert!(on.status.success(), "checked classify failed on {fixture_name}:\n{stderr}");
        let want = format!("KM_TIMING KM_FRONTEND_CHECK agreed procedure={procedure}");
        assert!(
            stderr.contains(&want),
            "expected `{want}` on {fixture_name} (lines={lines}), got:\n{stderr}"
        );
        assert!(stderr.contains("KM_TIMING KM_FRONTEND_CHECK_WALL ms="), "{stderr}");
        assert!(
            stderr.contains("KM_TIMING KM_FRONTEND_CHECK_PHASE phase=parse ms="),
            "{stderr}"
        );
        assert_eq!(on.stdout, off.stdout, "the check changed the answer on {fixture_name}");
    }
}

#[test]
fn frontend_check_agrees_on_el_existentials() {
    assert_agrees("el_existentials.ofn", "el");
}

#[test]
fn frontend_check_agrees_on_el_role_chain() {
    assert_agrees("el_role_chain.ofn", "el");
}

#[test]
fn frontend_check_agrees_on_el_unsatisfiable_classes() {
    assert_agrees("el_unsat_class.ofn", "el");
    assert_agrees("el_property_unsat.ofn", "el");
}

#[test]
fn frontend_check_agrees_on_el_inconsistent_ontology() {
    assert_agrees("el_tbox_inconsistent.ofn", "el");
}

#[test]
fn frontend_check_agrees_on_full_iris_and_owl_thing() {
    // Full IRIs (no prefix to expand), an equivalence with owl:Thing and a
    // subclass of owl:Nothing.
    assert_agrees("el_full_iris.ofn", "el");
}

#[test]
fn frontend_check_agrees_on_alc_disjunction() {
    assert_agrees("alc_disjunction.ofn", "alc");
}

#[test]
fn frontend_check_agrees_on_alc_unsatisfiable_class() {
    assert_agrees("alc_unsat.ofn", "alc");
}

/// The check declines with `reason` and the answer is published unchanged.
fn assert_declines(ont: &Path, checker_path: &Path, extra: &[(&str, &OsStr)], reason: &str) {
    let off = run_km(ont, true, &[]);
    assert!(off.status.success(), "{}", String::from_utf8_lossy(&off.stderr));
    let mut env = check_env(checker_path);
    env.extend_from_slice(extra);
    let on = run_km(ont, true, &env);
    let stderr = String::from_utf8_lossy(&on.stderr);
    assert!(on.status.success(), "a decline must not fail the run:\n{stderr}");
    let want = format!("KM_TIMING KM_FRONTEND_CHECK declined: {reason}");
    assert!(stderr.contains(&want), "expected `{want}`, got:\n{stderr}");
    assert_eq!(on.stdout, off.stdout, "a decline changed the answer");
}

#[test]
fn frontend_check_declines_outside_the_fragment() {
    let Some(checker_path) = checker() else {
        return;
    };
    // A nominal: outside F, the Lean parser rejects it.
    assert_declines(
        &fixture("rules_taxonomy.ofn"),
        &checker_path,
        &[],
        "parse rejected: out of fragment",
    );
    // A cardinality restriction.
    assert_declines(
        &fixture("alc_property_names.ofn"),
        &checker_path,
        &[],
        "parse rejected: out of fragment: ObjectMinCardinality",
    );
}

#[test]
fn frontend_check_declines_over_the_alc_budget() {
    let Some(checker_path) = checker() else {
        return;
    };
    assert_declines(&fixture("alc_budget.ofn"), &checker_path, &[], "alc budget:");
}

/// A stand-in checker: a POSIX shell script with `body`.
fn fake_checker(name: &str, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("frontend_check_fakes");
    std::fs::create_dir_all(&dir).expect("create fake checker dir");
    let path = dir.join(name);
    std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write fake checker");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("chmod fake checker");
    path
}

/// The check disagrees with `first`: nothing is published and km exits 6.
fn assert_fails_closed(ont: &Path, checker_path: &Path, first: &str) {
    for lines in [true, false] {
        let on = run_km(ont, lines, &check_env(checker_path));
        let stderr = String::from_utf8_lossy(&on.stderr);
        assert_eq!(
            on.status.code(),
            Some(6),
            "a disagreement must fail closed with exit 6 (lines={lines}):\n{stderr}"
        );
        assert!(on.stdout.is_empty(), "a disagreement must publish nothing");
        let want = format!("KM_TIMING KM_FRONTEND_CHECK disagreed: {first}");
        assert!(stderr.contains(&want), "expected `{want}`, got:\n{stderr}");
        assert!(
            stderr.contains("KM_FRONTEND_CHECK fail closed: km-owl-reference (procedure el) disagrees with the answer"),
            "{stderr}"
        );
        assert!(stderr.contains("no answer published"), "{stderr}");
    }
}

#[test]
fn frontend_check_disagreement_on_the_verdict_fails_closed() {
    let checker_path = fake_checker(
        "inconsistent.sh",
        r#"printf '{"format":"owl-sparse-v1","procedure":"el","inconsistent":true,"unsat":[],"rows":[]}\n'"#,
    );
    assert_fails_closed(
        &fixture("el_existentials.ofn"),
        &checker_path,
        "inconsistent: km=false reference=true",
    );
}

#[test]
fn frontend_check_disagreement_on_a_subsumption_fails_closed() {
    // The real answer of el_unsat_class.ofn without `A ⊑ B`.
    let checker_path = fake_checker(
        "missing_sub.sh",
        r#"n='http://example.org/ref/unsat#'
printf '{"format":"owl-sparse-v1","procedure":"el","inconsistent":false,"unsat":["%sU"],"rows":[{"sub":"%sA","sups":["%sA"]},{"sub":"%sB","sups":["%sB"]},{"sub":"%sC","sups":["%sC"]}]}\n' "$n" "$n" "$n" "$n" "$n" "$n" "$n""#,
    );
    assert_fails_closed(
        &fixture("el_unsat_class.ofn"),
        &checker_path,
        "SubClassOf(http://example.org/ref/unsat#A http://example.org/ref/unsat#B): km=yes reference=no",
    );
}

#[test]
fn frontend_check_disagreement_on_unsatisfiability_fails_closed() {
    let checker_path = fake_checker(
        "missing_unsat.sh",
        r#"n='http://example.org/ref/unsat#'
printf '{"format":"owl-sparse-v1","procedure":"el","inconsistent":false,"unsat":[],"rows":[]}\n'"#,
    );
    assert_fails_closed(
        &fixture("el_unsat_class.ofn"),
        &checker_path,
        "unsatisfiable http://example.org/ref/unsat#U: km=yes reference=no",
    );
}

#[test]
fn frontend_check_checker_failures_decline() {
    let ont = fixture("el_existentials.ofn");
    let failing = fake_checker(
        "decline.sh",
        "echo 'KM_REFERENCE_TIMING phase=read ms=0' >&2\necho 'not recognised: fake' >&2\nexit 3",
    );
    assert_declines(&ont, &failing, &[], "not recognised: fake (checker status: exit status: 3)");
    let garbage = fake_checker("garbage.sh", "echo '{\"format\":\"sparse-v1\"}'");
    assert_declines(&ont, &garbage, &[], "invalid checker output JSON");
    let slow = fake_checker("slow.sh", "sleep 5");
    assert_declines(
        &ont,
        &slow,
        &[("KM_FRONTEND_CHECK_BUDGET_S", OsStr::new("0.2"))],
        "budget",
    );
    let missing = Path::new(env!("CARGO_TARGET_TMPDIR")).join("frontend_check_fakes/absent");
    assert_declines(&ont, &missing, &[], "no km-owl-reference checker");
}

#[test]
fn frontend_check_is_off_by_default() {
    // A fake checker that would fail closed, but the switch is not set.
    let checker_path = fake_checker(
        "off.sh",
        r#"printf '{"format":"owl-sparse-v1","procedure":"el","inconsistent":true,"unsat":[],"rows":[]}\n'"#,
    );
    let ont = fixture("el_existentials.ofn");
    let off = run_km(&ont, true, &[("KM_OWL_REFERENCE_CHECKER", checker_path.as_os_str())]);
    assert!(off.status.success());
    let stderr = String::from_utf8_lossy(&off.stderr);
    assert!(!stderr.contains("KM_FRONTEND_CHECK"), "{stderr}");
    let zero = run_km(
        &ont,
        true,
        &[
            ("KM_FRONTEND_CHECK", OsStr::new("0")),
            ("KM_OWL_REFERENCE_CHECKER", checker_path.as_os_str()),
        ],
    );
    assert!(zero.status.success());
    assert_eq!(zero.stdout, off.stdout);
}
