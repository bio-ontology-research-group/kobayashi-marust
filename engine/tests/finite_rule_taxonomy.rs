use std::process::{Command, Output};

fn classify(source: &str, configure: impl FnOnce(&mut Command)) -> Output {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!("km-finite-taxonomy-{}-{unique}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for key in ["KM_FINITE_RULE_TAXONOMY", "KM_FINITE_DATA_RULE_NORMALIZE",
        "KM_RULE_JOIN_ORDER", "KM_RULE_ASSERTION_CLOSURE", "KM_TRANSITIVE_RULE_REDUCE"] {
        command.env_remove(key);
    }
    command.env_remove("KM_NO_FINITE_DATA_RULE_NORMALIZE")
        .env_remove("KM_NO_FINITE_RULE_TAXONOMY")
        .env_remove("KM_HT_LEAN_CERT_CHECKER")
        .args(["classify", "--route", "auto"]).arg(&path);
    configure(&mut command);
    let output = command.output().unwrap();
    std::fs::remove_file(path).unwrap();
    output
}

const SOURCE: &str = include_str!("fixtures/finite_rule_taxonomy.ofn");

#[test]
fn named_rule_conclusion_does_not_become_universal_subsumption() {
    let result = classify(SOURCE, |_| {});
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["subsumptions"], serde_json::json!([["http://km.test/P", "http://km.test/Q"]]));
}

#[test]
fn contradictory_rule_abox_cannot_publish_projection() {
    let source = SOURCE.replacen("Ontology(",
        "Ontology(ClassAssertion(ObjectComplementOf(<http://km.test/Bad>) <http://km.test/b>) ", 1);
    let result = classify(&source, |_| {});
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], false);
    assert_eq!(output["dropped"], 0);
}

#[test]
fn requested_ht_certificate_cannot_be_bypassed_by_finite_rule_projection() {
    let result = classify(SOURCE, |command| {
        command.env("KM_HT_LEAN_CERT_CHECKER", "/nonexistent-finite-rule-checker");
    });
    assert!(!result.status.success(), "unchecked projection bypassed requested HT certification");
}

/// A rule worker that prints `{}` must never be read as a consistent
/// verdict. Since v1.7.0 the default schedule answers this ontology by the
/// ground-rule reduction on the native bridge and never starts the rule
/// worker (docs/V1.7.0-RULES-SHOIQ.md); a certificate request (here
/// `KM_RULES_LEAN_CERT`) or `KM_RULES_ROUTE_FIRST=1` sends it to the rules
/// route first, as at v1.6.5, and there the empty verdict must fail the run.
#[cfg(unix)]
#[test]
fn missing_worker_verdict_cannot_default_to_consistent() {
    use std::os::unix::fs::PermissionsExt;
    let path = std::env::temp_dir().join(format!("km-empty-rule-worker-{}", std::process::id()));
    std::fs::write(&path, "#!/bin/sh\ncat >/dev/null\nprintf '{}\\n'\n").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let certificates = std::env::temp_dir().join(format!("km-empty-rule-worker-cert-{}", std::process::id()));
    // The default schedule does not consult the rule worker.
    let result = classify(SOURCE, |command| { command.env("KM_TAB_BIN", &path); });
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["subsumptions"], serde_json::json!([["http://km.test/P", "http://km.test/Q"]]));
    // The rules route reads the worker's verdict and refuses the empty one.
    for (key, value) in [("KM_RULES_ROUTE_FIRST", std::ffi::OsString::from("1")),
                         ("KM_RULES_LEAN_CERT", certificates.clone().into_os_string())] {
        let result = classify(SOURCE, |command| { command.env("KM_TAB_BIN", &path).env(key, &value); });
        assert!(!result.status.success(), "{key}: {}", String::from_utf8_lossy(&result.stdout));
        assert!(String::from_utf8_lossy(&result.stderr).contains("missing field `consistent`"),
            "{key}: {}", String::from_utf8_lossy(&result.stderr));
    }
    let _ = std::fs::remove_dir_all(certificates);
    std::fs::remove_file(path).unwrap();
}
