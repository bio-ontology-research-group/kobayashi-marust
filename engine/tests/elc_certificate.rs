use std::io::Write;
use std::process::{Command, Stdio};

const PURE_EL: &str = r#"{
  "clauses": [{
    "body": [{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}],
    "head": [{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}]
  }]
}"#;

fn run(checker: Option<&str>) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_elc"));
    command
        .env("KM_ELC_LEAN_REQUIRED", "1")
        .env_remove("KM_ELC_LEAN_CERT_CHECKER")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(checker) = checker {
        command.env("KM_ELC_LEAN_CERT_CHECKER", checker);
    }
    let mut child = command.spawn().expect("start ELC worker");
    child
        .stdin
        .take()
        .expect("ELC stdin")
        .write_all(PURE_EL.as_bytes())
        .expect("write ELC input");
    child.wait_with_output().expect("wait for ELC worker")
}

#[test]
fn certified_elc_publication_fails_closed_without_or_after_checker_rejection() {
    let missing = run(None);
    assert_eq!(missing.status.code(), Some(3));
    assert!(missing.stdout.is_empty(), "unchecked ELC result was published");

    let rejected = run(Some("/bin/false"));
    assert_eq!(rejected.status.code(), Some(3));
    assert!(rejected.stdout.is_empty(), "rejected ELC result was published");
}

#[test]
fn certified_elc_publication_passes_the_real_source_checker() {
    let Some(checker) = std::env::var_os("KM_ELC_TEST_LEAN_CHECKER") else {
        return;
    };
    let accepted = run(checker.to_str());
    assert!(accepted.status.success(), "{}", String::from_utf8_lossy(&accepted.stderr));
    let output: serde_json::Value =
        serde_json::from_slice(&accepted.stdout).expect("checked ELC JSON output");
    assert_eq!(output["inconsistent"], false);
    assert_eq!(output["subsumptions"]["A"], serde_json::json!(["B"]));
}

fn classify_with_failed_elc(route: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_km"))
        .args([
            "classify",
            "--route",
            route,
            concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/automatic_el_fallback.ofn"
            ),
        ])
        .env("KM_ELC_BIN", "/bin/false")
        .env("KM_NO_INPROC_ELC", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("run KM classification")
}

#[test]
fn automatic_el_decline_retries_exactly_but_forced_el_remains_atomic() {
    let automatic = classify_with_failed_elc("auto");
    assert!(
        automatic.status.success(),
        "{}",
        String::from_utf8_lossy(&automatic.stderr)
    );
    let output: serde_json::Value =
        serde_json::from_slice(&automatic.stdout).expect("automatic fallback output");
    assert_eq!(output["subsumptions"], serde_json::json!([[":A", ":B"]]));

    let forced = classify_with_failed_elc("elc");
    assert!(!forced.status.success());
    assert!(forced.stdout.is_empty(), "forced failed ELC published output");
}
