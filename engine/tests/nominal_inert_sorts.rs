//! Inert object sorts in the nominal CB input (docs/NOMINALS-CB.md, "Inert
//! object sorts in the nominal CB input (2026-10-30)").
//!
//! The sort encoding relativizes every `⊤` fact to `→ Q(x) ∨ D(x)`. On the
//! nominal-plus-data seeds of `gen_nomdata.py --no-inverse` the CB engine
//! carried the `D(x)` disjunct through the ground context; at v1.5.5's base
//! (87fda54f) the automatic route timed out on seeds 2032, 2058 and 2131
//! within 60 s. Releasing the object sort of definers whose sort no clause
//! can observe, and eliminating the definers that then hold everywhere,
//! answers them in seconds. `m2032_min` is seed 2032 reduced to the three
//! axioms that keep the time-out. Expected answers are HermiT 1.4.3.456's
//! (`*.hermit.json`).
use std::collections::BTreeSet;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(120);

type Answer = (bool, BTreeSet<String>, BTreeSet<(String, String)>);

fn strip(name: &str) -> String {
    name.trim_start_matches(':').rsplit('#').next().unwrap().to_string()
}

fn classify(path: &str, route: Option<&str>, env: &[(&str, &str)]) -> Answer {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let mut child = command
        .args(["classify", "--lines", path])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            let mut stdout = String::new();
            child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
            assert!(status.success(), "km failed on {path} {route:?}");
            let mut consistent = None;
            let mut unsat = BTreeSet::new();
            let mut subs = BTreeSet::new();
            for line in stdout.lines() {
                let fields: Vec<&str> = line.split('\t').collect();
                match fields.as_slice() {
                    [single] if single.starts_with("CONSISTENT ") => consistent = Some(single.ends_with(" 1")),
                    ["UNSAT", class] => {
                        unsat.insert(strip(class));
                    }
                    ["SUB", sub, sup] => {
                        subs.insert((strip(sub), strip(sup)));
                    }
                    _ => {}
                }
            }
            let consistent = consistent.expect("no CONSISTENT line");
            subs.retain(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b));
            return (consistent, unsat, subs);
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on {path} {route:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn hermit(name: &str) -> Answer {
    let path = fixture(&format!("{name}.hermit.json"));
    let value: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let consistent = value["consistent"].as_bool().unwrap();
    let unsat: BTreeSet<String> =
        value["unsatisfiable"].as_array().unwrap().iter().map(|v| strip(v.as_str().unwrap())).collect();
    let subs: BTreeSet<(String, String)> = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| (strip(pair[0].as_str().unwrap()), strip(pair[1].as_str().unwrap())))
        .filter(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b))
        .collect();
    (consistent, unsat, subs)
}

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/nominal_inert_sorts/{name}", env!("CARGO_MANIFEST_DIR"))
}

const FIXTURES: [&str; 3] = ["m2032_min", "m2058", "m2131"];

#[test]
fn released_sorts_answer_the_seeds_like_hermit_on_the_nominal_routes() {
    for name in FIXTURES {
        let expected = hermit(name);
        // The forced `nominals` route clausifies without trigger absorption;
        // on m2058 it stays above 120 s with the copy (cause not analysed;
        // the automatic route answers through `certified_nominals`).
        let routes: &[Option<&str>] = if name == "m2058" {
            &[None, Some("certified_nominals")]
        } else {
            &[None, Some("certified_nominals"), Some("nominals")]
        };
        for &route in routes {
            let got = classify(&fixture(&format!("{name}.ofn")), route, &[]);
            if expected.0 {
                assert_eq!(got, expected, "{name} on {route:?}");
            } else {
                assert!(!got.0, "{name} on {route:?}: HermiT says inconsistent");
            }
        }
    }
}

/// The stderr of a `nominals`-route run under `env`, stopped after `bound`.
fn stderr_of(path: &str, env: &[(&str, &str)], bound: Duration) -> String {
    let log = format!("{}/nominal_inert_sorts_{}.err", env!("CARGO_TARGET_TMPDIR"), env.len());
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_TIMING", "1").env("KM_ROUTE", "nominals");
    for (key, value) in env {
        command.env(key, value);
    }
    let mut child = command
        .args(["classify", "--lines", path])
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&log).unwrap())
        .spawn()
        .unwrap();
    let started = Instant::now();
    while child.try_wait().unwrap().is_none() && started.elapsed() < bound {
        std::thread::sleep(Duration::from_millis(20));
    }
    let _ = child.kill();
    let _ = child.wait();
    std::fs::read_to_string(&log).unwrap()
}

#[test]
fn certified_and_opted_out_cb_runs_keep_the_sorted_clauses() {
    // A run that must publish a CB Lean certificate keeps the clause set its
    // typed source describes, and `KM_CB_KEEP_INERT_SORTS` opts out; neither
    // makes the copy. The default run reports the release before the CB
    // engine starts.
    let path = fixture("m2032_min.ofn");
    let released = "nominal CB input: released";
    assert!(stderr_of(&path, &[], BOUND).contains(released));
    for keep in [("KM_CB_KEEP_INERT_SORTS", "1"), ("KM_CB_LEAN_REQUIRED", "1")] {
        let stderr = stderr_of(&path, &[keep], Duration::from_secs(10));
        assert!(!stderr.contains(released), "{keep:?}: {stderr}");
    }
}

#[test]
fn cb_release_certificate_is_accepted_by_the_lean_checker() {
    // The same `WireInertSortRelease` document as the rule checker's release,
    // with the CB variant's reservations, for the clause set after the
    // release and before the universal-definer elimination. The checker path
    // comes from `KM_RULES_TEST_INERT_LEAN_CHECKER` (as in
    // `rules_inert_sort_certificate`); without it the test skips unless
    // `KM_REQUIRE_LEAN_CHECKERS` is set.
    let Some(checker) = std::env::var_os("KM_RULES_TEST_INERT_LEAN_CHECKER") else {
        assert!(
            std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
            "KM_RULES_TEST_INERT_LEAN_CHECKER is required"
        );
        eprintln!("skipping: KM_RULES_TEST_INERT_LEAN_CHECKER is unset");
        return;
    };
    let mut certified = 0;
    for name in FIXTURES {
        let dir = std::env::temp_dir().join(format!("km-cb-inert-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let path = fixture(&format!("{name}.ofn"));
        let checked = classify(
            &path,
            None,
            &[
                ("KM_RULES_INERT_CERT", dir.to_str().unwrap()),
                ("KM_RULES_INERT_LEAN_CHECKER", checker.to_str().unwrap()),
                ("KM_TIMING", "1"),
            ],
        );
        assert_eq!(checked, classify(&path, None, &[]), "{name}: the certified run answered differently");
        let stderr = stderr_of(&path, &[("KM_RULES_INERT_CERT", dir.to_str().unwrap()),
            ("KM_RULES_INERT_LEAN_CHECKER", checker.to_str().unwrap()), ("KM_ROUTE", "certified_nominals")], BOUND);
        assert!(!stderr.contains("kept the frontend's clauses"), "{name}: {stderr}");
        // A certificate is written only when the release frees a definer
        // (m2058 gets the universal-definer elimination only).
        let released = stderr.contains("nominal CB input: released") && !stderr.contains("nominal CB input: released 0 ");
        let files = std::fs::read_dir(&dir).unwrap().count();
        assert_eq!(files > 0, released, "{name}: certificates {files}, release {released}");
        certified += usize::from(released);
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(certified >= 2, "only {certified} fixtures produced a checked certificate");
}

/// The Lean checker of the nominal CB input certificate
/// (`nominal-cb-input-check`, `WireNominalCBInput`), from
/// `KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER`; `None` skips unless
/// `KM_REQUIRE_LEAN_CHECKERS` is set.
fn nominal_cb_input_checker() -> Option<std::path::PathBuf> {
    match std::env::var_os("KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER") {
        Some(path) => Some(std::fs::canonicalize(path).unwrap()),
        None => {
            assert!(
                std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                "KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER is required"
            );
            eprintln!("skipping: KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER is unset");
            None
        }
    }
}

/// A checker directory for `KM_LEAN_CHECKERS` holding one executable named
/// `nominal-cb-input-check`. With `corrupt`, it is a wrapper that drops the
/// last clause of the certificate's `result` before the real checker reads
/// it, so the certificate no longer matches the release and elimination of
/// its `original`.
fn checker_dir(real: &std::path::Path, corrupt: bool) -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("nominal-cb-checkers-{}-{corrupt}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join("nominal-cb-input-check");
    if corrupt {
        let script = format!(
            "#!/bin/sh\npython3 -I -c 'import json, sys\np = sys.argv[1]\nd = json.load(open(p))\nd[\"result\"] = d[\"result\"][:-1]\njson.dump(d, open(p, \"w\"))' \"$1\" || exit 2\nexec '{}' \"$1\"\n",
            real.display()
        );
        std::fs::write(&exe, script).unwrap();
        std::fs::set_permissions(&exe, std::fs::Permissions::from_mode(0o755)).unwrap();
    } else {
        std::os::unix::fs::symlink(real, &exe).unwrap();
    }
    dir
}

/// Run `km classify --lines` on the forced `nominals` route (the atomic CB
/// worker reads the copy) and return its exit code, stdout and stderr.
fn run_nominals(path: &str, env: &[(&str, &std::ffi::OsStr)]) -> (Option<i32>, String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .env("KM_ROUTE", "nominals")
        .env("KM_TIMING", "1")
        .env("TMPDIR", env!("CARGO_TARGET_TMPDIR"));
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.args(["classify", "--lines", path]).output().unwrap();
    (
        output.status.code(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn nominal_cb_input_certificate_is_accepted_and_a_corrupted_one_fails_closed() {
    let Some(real) = nominal_cb_input_checker() else { return };
    let good = checker_dir(&real, false);
    let bad = checker_dir(&real, true);
    // m2032_min gets the release and the elimination, m2131 too; m2058 gets
    // the elimination only (no release certificate is written there).
    for name in ["m2032_min", "m2131"] {
        let path = fixture(&format!("{name}.ofn"));
        let (code, plain, _) = run_nominals(&path, &[]);
        assert_eq!(code, Some(0), "{name}: plain run failed");
        assert!(plain.contains("CONSISTENT "), "{name}: no answer");

        // KM_LEAN_CHECKERS with the real checker: accepted, same answer.
        let (code, checked, stderr) = run_nominals(&path, &[("KM_LEAN_CHECKERS", good.as_os_str())]);
        assert_eq!(code, Some(0), "{name}: {stderr}");
        assert_eq!(checked, plain, "{name}: the checked run answered differently");
        assert!(
            stderr.contains("KM_LEAN_CHECK accepted family=cb checker=nominal-cb-input-check"),
            "{name}: no accepted nominal CB input certificate: {stderr}"
        );
        assert!(!stderr.contains("KM_LEAN_CHECK rejected"), "{name}: {stderr}");

        // KM_LEAN_CHECKERS with a corrupted certificate: rejected, no answer.
        let (code, stdout, stderr) = run_nominals(&path, &[("KM_LEAN_CHECKERS", bad.as_os_str())]);
        assert_eq!(code, Some(6), "{name}: a rejected certificate must fail closed: {stderr}");
        assert!(!stdout.contains("CONSISTENT "), "{name}: an answer was published: {stdout}");
        assert!(
            stderr.contains("KM_LEAN_CHECK rejected family=cb checker=nominal-cb-input-check"),
            "{name}: {stderr}"
        );

        // The explicit variables: accepted with the real checker, and the
        // corrupted certificate fails the run instead of falling back to the
        // frontend's clauses.
        let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("nominal-cb-certs-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let (code, explicit, stderr) = run_nominals(
            &path,
            &[("KM_NOMINAL_CB_INPUT_CERT", dir.as_os_str()), ("KM_NOMINAL_CB_INPUT_LEAN_CHECKER", real.as_os_str())],
        );
        assert_eq!(code, Some(0), "{name}: {stderr}");
        assert_eq!(explicit, plain, "{name}: the certified run answered differently");
        assert!(std::fs::read_dir(&dir).unwrap().count() > 0, "{name}: no certificate written");
        let wrapper = bad.join("nominal-cb-input-check");
        let (code, stdout, stderr) = run_nominals(
            &path,
            &[("KM_NOMINAL_CB_INPUT_CERT", dir.as_os_str()), ("KM_NOMINAL_CB_INPUT_LEAN_CHECKER", wrapper.as_os_str())],
        );
        assert_ne!(code, Some(0), "{name}: a rejected certificate must fail the run: {stdout}");
        assert!(!stdout.contains("CONSISTENT "), "{name}: an answer was published: {stdout}");
        assert!(!stderr.contains("kept the frontend's clauses"), "{name}: {stderr}");
        let _ = std::fs::remove_dir_all(&dir);
    }
    let _ = std::fs::remove_dir_all(&good);
    let _ = std::fs::remove_dir_all(&bad);
}
