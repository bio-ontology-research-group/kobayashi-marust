//! The batch rule checker (`orchestrate::rules_consistency`) and the
//! incremental one (`incremental_rules::rules_consistent`) release the same
//! inert object sorts (docs/NOMINALS-CB.md section 6), and the rule-checker
//! worker does not depend on reserving gigabytes of stack up front
//! (`bigstack`).
//!
//! The fixture is seed fr69 of results/agents/2026-10-30/rules-worker-cost
//! (`gen_finite_rules.py`): the ore_ont_7278 shape, with `DataPropertyRange`
//! definers relativized by the sort encoding and a binary DL-safe rule with a
//! `swrlb` comparison, so the finite-rule grounding sets `KM_NOMINALS`.

use std::io::Write;
use std::process::{Command, Stdio};

const FIXTURE: &str = include_str!("fixtures/rules_inert_sorts_fr69.ofn");

/// A fresh input directory under Cargo's per-target scratch directory.
fn scratch_dir() -> std::path::PathBuf {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("km-inert-sorts-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The fixture plus one class assertion: a revision the incremental rule
/// adapter must re-check (an addition to a consistent ABox).
fn revised() -> String {
    let close = FIXTURE.rfind(')').expect("ontology close");
    format!(
        "{}ClassAssertion(<http://example.org/f#E> <http://example.org/f#d>)\n{}",
        &FIXTURE[..close],
        &FIXTURE[close..]
    )
}

/// The definer list of the first `KM_TIMING` line that contains `marker`.
fn released(stderr: &str, marker: &str) -> Option<Vec<String>> {
    let line = stderr.lines().find(|line| line.starts_with(marker))?;
    let (_, names) = line.rsplit_once("; released: ")?;
    Some(names.split(',').map(str::to_string).collect())
}

fn batch(source: &str, extra: &[(&str, &str)]) -> (String, String) {
    let dir = scratch_dir();
    let path = dir.join("input.ofn");
    std::fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.arg("classify").arg("--lines").arg(&path).env("KM_TIMING", "1");
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.output().expect("run km classify");
    std::fs::remove_dir_all(&dir).ok();
    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn incremental(commands: &[serde_json::Value], extra: &[(&str, &str)]) -> (Vec<serde_json::Value>, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command
        .arg("incremental-source")
        // `IncrementalRulesClassifier` belongs to the per-route adapter session.
        .env("KM_SOURCE_SESSION", "legacy")
        // The session keeps the rule adapter only when its frontend carries
        // every data assertion (`retained_backend_allowed`); without the
        // conversion a revision of this shape is an exact batch rebuild,
        // which runs `orchestrate::rules_consistency` itself.
        .env("KM_DATA_ASSERTION_AS_CLASS", "1")
        .env("KM_TIMING", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (key, value) in extra {
        command.env(key, value);
    }
    let mut child = command.spawn().expect("spawn km incremental-source");
    {
        let stdin = child.stdin.as_mut().expect("incremental stdin");
        for command in commands {
            serde_json::to_writer(&mut *stdin, command).unwrap();
            stdin.write_all(b"\n").unwrap();
        }
    }
    let output = child.wait_with_output().expect("wait for source session");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(output.status.success(), "stderr: {stderr}");
    let rows = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    (rows, stderr)
}

#[test]
fn incremental_and_batch_rule_checkers_release_the_same_definers() {
    let revision = revised();
    let (_, batch_err) = batch(&revision, &[]);
    let batch_released = released(&batch_err, "KM_TIMING rules-consistency released")
        .unwrap_or_else(|| panic!("the batch checker released nothing:\n{batch_err}"));
    assert!(!batch_released.is_empty());
    // The batch route converts the assertions in its second frontend pass;
    // requesting the conversion up front gives the same checker input.
    let (_, converted_err) = batch(&revision, &[("KM_DATA_ASSERTION_AS_CLASS", "1")]);
    assert_eq!(released(&converted_err, "KM_TIMING rules-consistency released"), Some(batch_released.clone()));

    let commands = [
        serde_json::json!({"op": "init", "functional_syntax": FIXTURE}),
        serde_json::json!({"op": "replace", "functional_syntax": revision}),
    ];
    let (rows, incremental_err) = incremental(&commands, &[]);
    assert_eq!(rows.len(), 2, "{rows:#?}");
    assert_eq!(rows[0]["route"], "ht_rules", "{rows:#?}");
    assert_eq!(rows[1]["receipt"]["strategy"], "ht_delta", "{rows:#?}");
    let incremental_released = released(&incremental_err, "KM_TIMING incremental rules-consistency released")
        .unwrap_or_else(|| panic!("the incremental checker released nothing:\n{incremental_err}"));
    assert_eq!(incremental_released, batch_released);

    // The switch turns the pass off on both routes, and the verdict stays.
    let keep = [("KM_RULES_KEEP_INERT_SORTS", "1")];
    let (kept_rows, kept_err) = incremental(&commands, &keep);
    assert!(released(&kept_err, "KM_TIMING incremental rules-consistency released").is_none(), "{kept_err}");
    assert_eq!(kept_rows[1]["result"], rows[1]["result"]);
    let (_, kept_batch_err) = batch(&revision, &keep);
    assert!(released(&kept_batch_err, "KM_TIMING rules-consistency released").is_none());
}

#[test]
fn incremental_verdict_matches_batch_on_the_revision() {
    let revision = revised();
    let (batch_out, _) = batch(&revision, &[]);
    let commands = [
        serde_json::json!({"op": "init", "functional_syntax": FIXTURE}),
        serde_json::json!({"op": "replace", "functional_syntax": revision}),
    ];
    let (rows, _) = incremental(&commands, &[]);
    let batch_consistent = !batch_out.lines().any(|line| line.trim() == "INCONSISTENT")
        && !batch_out.contains("CONSISTENT 0");
    assert_eq!(rows[1]["result"]["consistent"], batch_consistent, "batch:\n{batch_out}\nrows: {rows:#?}");
}

/// Seed b11_1134 of the 2026-10-30 inert-sort review (`gen_wide2.py`): the
/// rule checker releases one sort and finds the ABox inconsistent, so the
/// classification ends with the checker and no other worker runs.
const INCONSISTENT_FIXTURE: &str = include_str!("fixtures/rules_inert_sorts_b11_1134.ofn");

/// Under an address-space limit of 3 GiB the old worker could not start its
/// 2 GiB + 4 GiB stack threads (`tableau error: Resource temporarily
/// unavailable`), the same failure strict overcommit produces under load.
/// The worker now grows its main-thread stack on demand. (The fixture ends
/// at the rule checker: other workers reserve address space for their own
/// allocator arenas, which an address-space limit counts but the commit
/// limit does not.)
#[cfg(target_os = "linux")]
#[test]
fn rule_checker_worker_runs_without_reserving_its_deep_stack() {
    use std::os::unix::process::CommandExt as _;
    let (unlimited_out, unlimited_err) = batch(INCONSISTENT_FIXTURE, &[]);
    assert!(released(&unlimited_err, "KM_TIMING rules-consistency released").is_some(), "{unlimited_err}");
    let dir = scratch_dir();
    let path = dir.join("input.ofn");
    std::fs::write(&path, INCONSISTENT_FIXTURE).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.arg("classify").arg("--lines").arg(&path).env("KM_TIMING", "1");
    unsafe {
        command.pre_exec(|| {
            let limit = libc::rlimit { rlim_cur: 3 << 30, rlim_max: 3 << 30 };
            if libc::setrlimit(libc::RLIMIT_AS, &limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let output = command.output().expect("run km classify");
    std::fs::remove_dir_all(&dir).ok();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stderr: {stderr}");
    assert!(stderr.contains("rules-consistency worker exited"), "{stderr}");
    assert_eq!(String::from_utf8_lossy(&output.stdout), unlimited_out);
}
