//! Conditional-full ABox schedule (`KM_HT_NATIVE_FULL=1`) against HermiT.
//!
//! Each fixture `tests/fixtures/conditional_full/<name>.ofn` is a minimized
//! fuzz case; `<name>.expected.json` is HermiT's classification of it
//! (consistency, named subsumptions, unsatisfiable classes). The cases cover:
//!
//! - the retained deterministic base taken while deterministic work was still
//!   queued (class jobs start with cleared queues);
//! - representative-association replay blocking the expansion of individuals
//!   whose association holds nondeterministic content;
//! - per-job class tableaux on singleton domains (inverse-functional roles
//!   into a nominal), which need the merge relocation and queue fixes.
use std::collections::BTreeSet;
use std::process::Command;

const CASES: &[&str] = &[
    "retained_base_pending_successor",
    "retained_base_pending_nominal_merge",
    "replay_blocking_nondeterministic_association",
    "replay_base_incomplete",
    "replay_anonymous_predecessor",
    "per_job_singleton_domain",
    "per_job_singleton_domain_typed",
    "fuzz_mm_27_223_0",
    "cw_min1002",
    "cw_min1002b",
    "cw_min1002c",
    "cw_min1002d",
    "cw_case1002",
    "cw_min4051",
    "cw_case4051",
    "cw_case4056",
    "fuzz_m170_full_revision",
    "fuzz_seed_0",
    "fuzz_seed_45",
    "fuzz_seed_1002",
    "fuzz_seed_2040",
    "fuzz_seed_3007",
    "fuzz_seed_3043",
    "fuzz_seed_4000",
    "fuzz_seed_4041",
    "fuzz_seed_4050",
    "fuzz_seed_4056",
    "fuzz_seed_5027",
    "fuzz_mm_110_364_3_base",
    "fuzz_mm_111_197_3_base",
    "fuzz_mm_111_197_3_revision",
    "fuzz_mm_111_23_1_base",
    "fuzz_mm_111_23_1_revision",
];

fn short(name: &str) -> String {
    name.rsplit(['/', '#']).next().unwrap_or(name).trim_start_matches(':').to_string()
}

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

fn normalise(value: &serde_json::Value) -> Answer {
    let consistent = value["consistent"].as_bool().unwrap();
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = value["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| short(v.as_str().unwrap()))
        .collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| {
            (
                short(pair[0].as_str().unwrap()),
                short(pair[1].as_str().unwrap()),
            )
        })
        .filter(|(sub, sup)| !unsat.contains(sub) && sub != sup && sup != "Thing")
        .collect();
    (true, subs, unsat)
}

fn classify(path: &str) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let result = command
        .args(["classify", path])
        .env("KM_ROUTE", "auto")
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_HT_DDB", "1")
        .env("KM_CACHE_CONFORMANCE", "1")
        .env("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1")
        .env("KM_FAST_IRI_GRAMMAR", "1")
        .env("KM_THREADS", "1")
        .output()
        .expect("run km classification");
    assert!(
        result.status.success(),
        "{path}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&result.stdout).unwrap()
}

#[test]
fn conditional_full_abox_cases_match_hermit() {
    let dir = format!(
        "{}/tests/fixtures/conditional_full",
        env!("CARGO_MANIFEST_DIR")
    );
    let mut failures = Vec::new();
    for case in CASES {
        let expected: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(format!("{dir}/{case}.expected.json")).unwrap(),
        )
        .unwrap();
        let actual = classify(&format!("{dir}/{case}.ofn"));
        let (expected, actual) = (normalise(&expected), normalise(&actual));
        if expected != actual {
            failures.push(format!(
                "{case}: missing {:?}, extra {:?}, consistent {} vs {}",
                expected.1.difference(&actual.1).collect::<Vec<_>>(),
                actual.1.difference(&expected.1).collect::<Vec<_>>(),
                actual.0,
                expected.0
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
