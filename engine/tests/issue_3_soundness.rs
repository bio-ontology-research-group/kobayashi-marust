use std::path::PathBuf;
use std::process::Command;

#[test]
fn nominal_enumeration_equality_reports_inconsistent() {
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue_3_nominal_different.ofn");
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--lines"])
        .arg(fixture)
        .output()
        .expect("run km classify");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 output");
    assert!(
        stdout.lines().any(|line| line == "CONSISTENT 0"),
        "{stdout}"
    );
    assert!(stdout.lines().any(|line| line == "DROPPED 0"), "{stdout}");
}
