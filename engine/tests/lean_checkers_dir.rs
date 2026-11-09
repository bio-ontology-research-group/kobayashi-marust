//! `KM_LEAN_CHECKERS=<dir>` (engine/src/lean_checkers.rs): an accepted
//! certificate leaves the answer unchanged and says so on stderr; a rejected
//! certificate makes `km classify` publish nothing and say why.
//!
//! The stub tests always run: their checker directory holds shell scripts
//! that accept or reject. The real-checker tests run only when
//! `KM_TEST_LEAN_CHECKERS_DIR` names a directory of built Lean checkers
//! (`lean/.lake/build/bin`); they corrupt a genuine certificate before the
//! genuine checker reads it.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const EL: &str = "Prefix(:=<http://example.org/lc#>)
Ontology(
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  SubClassOf(:A :B)
  SubClassOf(:B :C)
)
";

/// Not EL (a disjunction), so the CB worker answers.
const DISJUNCTIVE: &str = "Prefix(:=<http://example.org/lc#>)
Ontology(
  Declaration(Class(:A))
  Declaration(Class(:B))
  Declaration(Class(:C))
  Declaration(Class(:D))
  SubClassOf(:A ObjectUnionOf(:B :C))
  SubClassOf(:B :D)
  SubClassOf(:C :D)
)
";

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("lean-checkers-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn script(dir: &Path, name: &str, body: &str) {
    let path = dir.join(name);
    std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
}

fn classify(ontology: &Path, checkers: Option<&Path>, tmp: &Path) -> Output {
    classify_route(ontology, checkers, tmp, "auto")
}

/// `route` other than `auto` forces it; the CB tests force `cb_plain1` so
/// that the CB worker, not the race's HT-first probe, answers.
fn classify_route(ontology: &Path, checkers: Option<&Path>, tmp: &Path, route: &str) -> Output {
    classify_route_env(ontology, checkers, tmp, route, &[])
}

fn classify_route_env(
    ontology: &Path,
    checkers: Option<&Path>,
    tmp: &Path,
    route: &str,
    extra: &[(&str, &str)],
) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command
        .args(["classify", "--route", route, "--lines"])
        .arg(ontology)
        .env("TMPDIR", tmp)
        .env("KM_THREADS", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    if let Some(dir) = checkers {
        command.env("KM_LEAN_CHECKERS", dir);
    }
    for (key, value) in extra {
        command.env(key, value);
    }
    command.output().expect("run km classify")
}

fn sorted_lines(output: &Output) -> Vec<String> {
    let mut lines: Vec<String> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    lines.sort();
    lines
}

fn assert_fails_closed(output: &Output, family: &str) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(6), "{stderr}");
    assert!(
        output.stdout.is_empty(),
        "a rejected run published an answer"
    );
    assert!(stderr.contains("KM_LEAN_CHECKERS fail closed"), "{stderr}");
    assert!(
        stderr.contains(&format!("KM_LEAN_CHECK rejected family={family}")),
        "{stderr}"
    );
}

fn assert_accepted_unchanged(off: &Output, on: &Output, family: &str) {
    let stderr = String::from_utf8_lossy(&on.stderr);
    assert!(on.status.success(), "{stderr}");
    assert_eq!(
        sorted_lines(off),
        sorted_lines(on),
        "the checker changed the answer"
    );
    assert!(
        stderr.contains(&format!("KM_LEAN_CHECK accepted family={family}")),
        "{stderr}"
    );
    assert!(stderr.contains("KM_LEAN_CHECK summary"), "{stderr}");
}

#[test]
fn stub_elc_rejection_fails_closed_although_the_fallback_answers() {
    let work = scratch("stub-elc");
    let ontology = work.join("el.ofn");
    std::fs::write(&ontology, EL).unwrap();
    let off = classify(&ontology, None, &work);
    assert!(
        off.status.success(),
        "{}",
        String::from_utf8_lossy(&off.stderr)
    );

    let accept = work.join("accept");
    std::fs::create_dir_all(&accept).unwrap();
    script(&accept, "elc-cert-check", "exit 0");
    let on = classify(&ontology, Some(&accept), &work);
    assert_accepted_unchanged(&off, &on, "elc");

    let reject = work.join("reject");
    std::fs::create_dir_all(&reject).unwrap();
    script(
        &reject,
        "elc-cert-check",
        "echo 'stub rejection' >&2; exit 1",
    );
    let rejected = classify(&ontology, Some(&reject), &work);
    assert_fails_closed(&rejected, "elc");
    std::fs::remove_dir_all(&work).unwrap();
}

#[test]
fn stub_cb_acceptance_keeps_the_answer_and_rejection_fails_closed() {
    let work = scratch("stub-cb");
    let ontology = work.join("disjunctive.ofn");
    std::fs::write(&ontology, DISJUNCTIVE).unwrap();
    let off = classify_route(&ontology, None, &work, "cb_plain1");
    assert!(
        off.status.success(),
        "{}",
        String::from_utf8_lossy(&off.stderr)
    );

    let accept = work.join("accept");
    std::fs::create_dir_all(&accept).unwrap();
    script(&accept, "cb-source-taxonomy-cert-check", "exit 0");
    let on = classify_route(&ontology, Some(&accept), &work, "cb_plain1");
    assert_accepted_unchanged(&off, &on, "cb");

    let reject = work.join("reject");
    std::fs::create_dir_all(&reject).unwrap();
    script(&reject, "cb-source-taxonomy-cert-check", "exit 1");
    let rejected = classify_route(&ontology, Some(&reject), &work, "cb_plain1");
    assert_fails_closed(&rejected, "cb");
    std::fs::remove_dir_all(&work).unwrap();
}

/// Checkers-on defect B1: the legacy live wires decode a global-model
/// certificate that production never builds, so `KM_LEAN_CHECKERS_SET=all`
/// must not run them (they could only fail to decode) and records
/// `cannot_check` for each instead. The stubs reject, so running any of them
/// would fail the run closed.
#[test]
fn stub_set_all_declines_the_global_model_wires() {
    let work = scratch("stub-global-model");
    let ontology = work.join("disjunctive.ofn");
    std::fs::write(&ontology, DISJUNCTIVE).unwrap();
    let off = classify_route(&ontology, None, &work, "cb_plain1");
    assert!(
        off.status.success(),
        "{}",
        String::from_utf8_lossy(&off.stderr)
    );
    let dir = work.join("checkers");
    std::fs::create_dir_all(&dir).unwrap();
    script(&dir, "cb-source-taxonomy-cert-check", "exit 0");
    let legacy = [
        "cb-live-taxonomy-publication-check",
        "cb-live-exact-taxonomy-publication-check",
        "cb-terminal-state-check",
    ];
    for name in legacy {
        script(&dir, name, "echo 'legacy wire ran' >&2; exit 1");
    }
    let on = classify_route_env(
        &ontology,
        Some(&dir),
        &work,
        "cb_plain1",
        &[("KM_LEAN_CHECKERS_SET", "all")],
    );
    assert_accepted_unchanged(&off, &on, "cb");
    let stderr = String::from_utf8_lossy(&on.stderr);
    assert!(!stderr.contains("legacy wire ran"), "{stderr}");
    assert!(!stderr.contains("KM_LEAN_CHECK rejected"), "{stderr}");
    for name in legacy {
        assert!(
            stderr.contains(&format!("certificate={name}")),
            "no cannot_check event for {name}: {stderr}"
        );
    }
    std::fs::remove_dir_all(&work).unwrap();
}

#[test]
fn a_missing_checker_directory_is_a_usage_error() {
    let work = scratch("missing");
    let ontology = work.join("el.ofn");
    std::fs::write(&ontology, EL).unwrap();
    let output = classify(&ontology, Some(&work.join("absent")), &work);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    std::fs::remove_dir_all(&work).unwrap();
}

fn real_checkers() -> Option<PathBuf> {
    let dir = std::env::var_os("KM_TEST_LEAN_CHECKERS_DIR")?;
    Some(PathBuf::from(dir))
}

/// A checker directory whose `name` corrupts the certificate with `sed`
/// before handing it to the genuine checker of the same name.
fn corrupting_dir(work: &Path, real: &Path, name: &str, sed: &str) -> PathBuf {
    let dir = work.join(format!("corrupt-{name}"));
    std::fs::create_dir_all(&dir).unwrap();
    let real_checker = real.join(name);
    assert!(real_checker.is_file(), "missing {}", real_checker.display());
    script(
        &dir,
        name,
        &format!(
            "sed -i -e '{sed}' \"$1\" || exit 2\nexec '{}' \"$1\"",
            real_checker.display()
        ),
    );
    dir
}

#[test]
fn real_elc_checker_accepts_and_rejects_a_corrupted_certificate() {
    let Some(real) = real_checkers() else {
        eprintln!("skipped: KM_TEST_LEAN_CHECKERS_DIR not set");
        return;
    };
    let work = scratch("real-elc");
    let ontology = work.join("el.ofn");
    std::fs::write(&ontology, EL).unwrap();
    let off = classify(&ontology, None, &work);
    assert!(off.status.success());
    let on = classify(&ontology, Some(&real), &work);
    assert_accepted_unchanged(&off, &on, "elc");
    // Claim B below A in the published named taxonomy.
    let corrupt = corrupting_dir(
        &work,
        &real,
        "elc-cert-check",
        r#"s/"public_named_subsumptions":\[{"sub":"\([^"]*\)","sup":"\([^"]*\)"}/"public_named_subsumptions":[{"sub":"\2","sup":"\1"}/"#,
    );
    let rejected = classify(&ontology, Some(&corrupt), &work);
    assert_fails_closed(&rejected, "elc");
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("ELC certificate rejected"),
        "{}",
        String::from_utf8_lossy(&rejected.stderr)
    );
    std::fs::remove_dir_all(&work).unwrap();
}

#[test]
fn real_cb_checker_accepts_and_rejects_a_corrupted_certificate() {
    let Some(real) = real_checkers() else {
        eprintln!("skipped: KM_TEST_LEAN_CHECKERS_DIR not set");
        return;
    };
    let work = scratch("real-cb");
    let ontology = work.join("disjunctive.ofn");
    std::fs::write(&ontology, DISJUNCTIVE).unwrap();
    let off = classify_route(&ontology, None, &work, "cb_plain1");
    assert!(off.status.success());
    let only_source_exact = work.join("source-exact");
    std::fs::create_dir_all(&only_source_exact).unwrap();
    std::os::unix::fs::symlink(
        real.join("cb-source-taxonomy-cert-check"),
        only_source_exact.join("cb-source-taxonomy-cert-check"),
    )
    .unwrap();
    let on = classify_route(&ontology, Some(&only_source_exact), &work, "cb_plain1");
    assert_accepted_unchanged(&off, &on, "cb");
    // Claim the first non-entailed cell (A below B, refuted by a countermodel
    // in the same document) as entailed.
    let corrupt = corrupting_dir(
        &work,
        &real,
        "cb-source-taxonomy-cert-check",
        r#"s/"answer":false/"answer":true/"#,
    );
    let rejected = classify_route(&ontology, Some(&corrupt), &work, "cb_plain1");
    assert_fails_closed(&rejected, "cb");
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("CB taxonomy rejected"),
        "{}",
        String::from_utf8_lossy(&rejected.stderr)
    );
    std::fs::remove_dir_all(&work).unwrap();
}
