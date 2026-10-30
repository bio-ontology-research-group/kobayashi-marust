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
