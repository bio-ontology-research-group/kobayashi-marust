//! Regressions for the termination and search cost of Konclude's NN-rule in
//! the native bridge (docs/HYBRID-CB-HT.md section 24,
//! results/agents/2026-11-04/bridge-nn-term).
//!
//! Six family seeds of `gen_nn.py`: five that the base answered and the first
//! NN-rule port (48a1113b) did not answer within the family's 30 s and 60 s
//! caps (`nn346`, `nn952`, `nn745`, `nn1957`, `nn777`), and `nn1153`, which
//! needed the descriptor track point in `try_initializing_concept_from_saturated_data`
//! (`completion/u17.rs`) once leaf jobs stopped backtracking chronologically.
//! The port of Konclude's per-candidate distinct-set decisions, the leaf-job
//! unattributed-clash exit, and the saturated-initialisation track point
//! answer each in well under a second.
//!
//! Each fixture must agree with HermiT 1.4 (`.hermit.json`) on the
//! automatic route and on `ht_bridge`, and every classification must end
//! within `LIMIT`; the limit leaves room for a loaded host and is far below
//! the 30 s at which the first port timed out.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

const LIMIT: Duration = Duration::from_secs(20);

fn names(value: &serde_json::Value) -> Vec<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap().trim_start_matches(':').to_string())
        .collect()
}

/// Consistency, the subsumptions between satisfiable distinct classes, and
/// the unsatisfiable classes. An inconsistent answer carries nothing else.
fn normalise(value: &serde_json::Value) -> Answer {
    let consistent = value["consistent"].as_bool().unwrap();
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = names(&value["unsatisfiable"]).into_iter().collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| {
            let pair = names(pair);
            (pair[0].clone(), pair[1].clone())
        })
        .filter(|(sub, sup)| sub != sup && !unsat.contains(sub) && !unsat.contains(sup))
        .collect();
    (true, subs, unsat)
}

/// `km classify`, killed after `LIMIT`; `None` on a timeout.
fn classify(path: &Path, env: &[(&str, &str)]) -> Option<serde_json::Value> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let mut child = command
        .arg("classify")
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("run km classification");
    let mut stdout = child.stdout.take().unwrap();
    let reader = std::thread::spawn(move || {
        let mut out = Vec::new();
        stdout.read_to_end(&mut out).unwrap();
        out
    });
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "{}: exit {status}", path.display());
            let out = reader.join().unwrap();
            return Some(serde_json::from_slice(&out).unwrap());
        }
        if start.elapsed() > LIMIT {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn fixtures() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_nn_term");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "ofn"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "missing fixtures in {}", dir.display());
    paths
}

fn expected(path: &Path) -> Answer {
    let gold = path.with_extension("hermit.json");
    normalise(&serde_json::from_str(&std::fs::read_to_string(gold).unwrap()).unwrap())
}

const RELEASE: [(&str, &str); 6] = [
    ("KM_HT_DDB", "1"),
    ("KM_HT_NATIVE_FULL", "1"),
    ("KM_CACHE_CONFORMANCE", "1"),
    ("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1"),
    ("KM_FAST_IRI_GRAMMAR", "1"),
    ("KM_THREADS", "1"),
];

fn check(label: &str, extra: &[(&'static str, &'static str)]) {
    let env: Vec<(&str, &str)> = RELEASE.iter().copied().chain(extra.iter().copied()).collect();
    let mut wrong = Vec::new();
    for path in fixtures() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        match classify(&path, &env) {
            None => wrong.push(format!("{name} [{label}]: no answer within {LIMIT:?}")),
            Some(value) => {
                let got = normalise(&value);
                let want = expected(&path);
                if got != want {
                    wrong.push(format!("{name} [{label}]: got {got:?}, HermiT {want:?}"));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn automatic_route_answers_as_hermit_in_time() {
    for _ in 0..3 {
        check("auto", &[]);
    }
}

#[test]
fn forced_bridge_answers_as_hermit_in_time() {
    for _ in 0..3 {
        check("ht_bridge", &[("KM_ROUTE", "ht_bridge")]);
    }
}
