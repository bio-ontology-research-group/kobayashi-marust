//! Both `km incremental-source` session modes must answer the sort-encoding
//! reproducers exactly like `km classify --route auto` (HermiT 1.4's answer is
//! the `.hermit` file next to each fixture).
//!
//! The legacy session (`KM_SOURCE_SESSION=legacy`) normalizes the source
//! without the `DataHasValue` conversion of data-property assertions that the
//! batch pipeline applies on demand, and its retained backends then classified
//! a clause set without the three `u` values: `⊤ ⊑ ≤2 u` with three values on
//! one individual (`max2_three.ofn`) was answered `consistent: true,
//! dropped: 0`. A revision with uncarried data assertions is now classified by
//! the exact automatic pipeline alone, at initialization and on replacement.
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sorts_differential").join(name)
}

fn hermit_consistent(path: &Path) -> bool {
    let reference = std::fs::read_to_string(path.with_extension("hermit")).unwrap();
    reference.lines().find_map(|line| line.strip_prefix("C\t")).expect("C line") == "true"
}

/// The responses of one session over `revisions` (init, then replace).
fn session(revisions: &[&str], legacy: bool) -> Vec<serde_json::Value> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if legacy {
        command.env("KM_SOURCE_SESSION", "legacy");
    }
    let mut child = command
        .arg("incremental-source")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    {
        let mut stdin = child.stdin.take().unwrap();
        for (index, source) in revisions.iter().enumerate() {
            let op = if index == 0 { "init" } else { "replace" };
            serde_json::to_writer(&mut stdin, &serde_json::json!({"op": op, "functional_syntax": source}))
                .unwrap();
            stdin.write_all(b"\n").unwrap();
        }
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

fn classify_auto(path: &Path) -> bool {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let output = command.args(["classify", "--lines", "--route", "auto"]).arg(path).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8(output.stdout).unwrap();
    stdout.lines().next() == Some("CONSISTENT 1")
}

#[test]
fn max2_reproducers_are_inconsistent_in_both_session_modes() {
    for name in ["max2_three.ofn", "max2_three_K.ofn"] {
        let path = fixture(name);
        let source = std::fs::read_to_string(&path).unwrap();
        assert!(!hermit_consistent(&path), "{name}");
        assert!(!classify_auto(&path), "{name}: km classify --route auto");
        for legacy in [false, true] {
            let rows = session(&[&source], legacy);
            assert_eq!(rows[0]["status"], "ok", "{name} legacy={legacy}: {}", rows[0]);
            assert_eq!(rows[0]["result"]["consistent"], false, "{name} legacy={legacy}: {}", rows[0]);
        }
    }
}

/// The same reproducer reached by replacing a consistent revision (`≤2 u`
/// with two values, `max2_two.ofn`) must not reuse the retained backend.
#[test]
fn replacing_into_the_reproducer_is_inconsistent_in_both_session_modes() {
    let two = std::fs::read_to_string(fixture("max2_two.ofn")).unwrap();
    let three = std::fs::read_to_string(fixture("max2_three.ofn")).unwrap();
    assert!(hermit_consistent(&fixture("max2_two.ofn")));
    for legacy in [false, true] {
        let rows = session(&[&two, &three, &two], legacy);
        assert_eq!(rows.len(), 3, "legacy={legacy}: {rows:?}");
        for row in &rows {
            assert_eq!(row["status"], "ok", "legacy={legacy}: {row}");
        }
        assert_eq!(rows[0]["result"]["consistent"], true, "legacy={legacy}: {}", rows[0]);
        assert_eq!(rows[1]["result"]["consistent"], false, "legacy={legacy}: {}", rows[1]);
        assert_eq!(rows[2]["result"]["consistent"], true, "legacy={legacy}: {}", rows[2]);
    }
}
