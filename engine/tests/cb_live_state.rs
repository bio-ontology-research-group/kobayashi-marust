use std::io::Write;
use std::process::{Command, Stdio};

fn snapshot_path(label: &str) -> std::path::PathBuf {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join(".work/artifacts");
    std::fs::create_dir_all(&root).unwrap();
    root.join(format!("cb-live-{label}-{}.json", std::process::id()))
}

#[test]
fn cli_emits_one_exact_terminal_engine_for_certification() {
    let path = snapshot_path("accepted");
    let input = r#"{"clauses":[{"body":[],"head":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}]}]}"#;
    let mut child = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LIVE_STATE", &path)
        .env("KM_THREADS", "4")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let snapshot: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    std::fs::remove_file(&path).unwrap();
    assert_eq!(snapshot["version"], 3);
    assert!(snapshot["comp_ind_bits"]
        .as_u64()
        .is_some_and(|bits| (1..32).contains(&bits)));
    assert!(snapshot["ordinary_clause_arena"].is_array());
    assert!(snapshot["root_clause_arena"].is_array());
    assert_eq!(snapshot["pending_messages"], 0);
    assert_eq!(snapshot["message_truncated"], false);
    assert_eq!(snapshot["nominal_truncated"], false);
    let contexts = snapshot["contexts"].as_array().unwrap();
    assert!(!contexts.is_empty());
    for (index, context) in contexts.iter().enumerate() {
        assert_eq!(context["context_index"], index);
        assert_eq!(context["context_id"], index);
        assert_eq!(context["todo_clause_ids"].as_array().unwrap().len(), 0);
        assert_eq!(context["dirty"], false);
        assert_eq!(
            context["pred_hwm"],
            context["pred_pool_ids"].as_array().unwrap().len()
        );
        assert_eq!(
            context["succ_hwm"],
            context["succ_pool_ids"].as_array().unwrap().len()
        );
        assert_eq!(
            context["rsucc_hwm"],
            context["rsucc_pool_ids"].as_array().unwrap().len()
        );
        assert_eq!(
            context["predecessor_edge_seen"],
            serde_json::Value::Array(
                context["predecessors"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|edge| edge["edge_seen"].clone())
                    .collect()
            )
        );
        assert_eq!(
            context["successor_reach_hwm"],
            serde_json::Value::Array(
                context["successors"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|edge| edge["rsucc_reach_hwm"].clone())
                    .collect()
            )
        );
    }
}

#[test]
fn unsupported_certification_schedule_fails_without_publishing() {
    let path = snapshot_path("split");
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LIVE_STATE", &path)
        .env("KM_SPLIT", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            child.stdin.take().unwrap().write_all(b"{\"clauses\":[]}")?;
            child.wait_with_output()
        })
        .unwrap();
    assert_eq!(output.status.code(), Some(5));
    assert!(output.stdout.is_empty());
    assert!(!path.exists());
}

#[test]
fn mandatory_lean_mode_fails_without_complete_configuration() {
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            child.stdin.take().unwrap().write_all(b"{\"clauses\":[]}")?;
            child.wait_with_output()
        })
        .unwrap();
    assert_eq!(output.status.code(), Some(5));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("KM_CB_GLOBAL_MODEL_CERT"));
}

#[test]
fn mandatory_lean_rejection_prevents_publication() {
    let global = snapshot_path("global-model");
    let bundle = snapshot_path("bundle");
    let derivation = snapshot_path("derivation-candidate");
    std::fs::write(&global, b"{}\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_GLOBAL_MODEL_CERT", &global)
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/false")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env("KM_CB_DERIVATION_CANDIDATE", &derivation)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            child.stdin.take().unwrap().write_all(
                br#"{"clauses":[{"body":[],"head":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}]}]}"#,
            )?;
            child.wait_with_output()
        })
        .unwrap();
    assert_eq!(output.status.code(), Some(5));
    assert!(output.stdout.is_empty());
    assert!(bundle.exists());
    assert!(derivation.exists());
    let document: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&bundle).unwrap()).unwrap();
    assert_eq!(document["version"], 1);
    assert_eq!(document["live_state"]["version"], 3);
    let history = document["live_state"]["insertion_history"]
        .as_array()
        .unwrap();
    assert!(!history.is_empty());
    let mut saw_core = false;
    let mut saw_ontology_fact = false;
    for (sequence, event) in history.iter().enumerate() {
        assert_eq!(event["sequence"], sequence);
        let root = event["root"].as_bool().unwrap();
        let arena = if root {
            &document["live_state"]["root_clause_arena"]
        } else {
            &document["live_state"]["ordinary_clause_arena"]
        };
        assert!(event["clause_id"].as_u64().unwrap() < arena.as_array().unwrap().len() as u64);
        let origin = event["origin_hint"].as_str().unwrap();
        assert!(matches!(origin, "core" | "ontology_fact" | "derived"));
        assert_eq!(event["origin_index"].is_number(), origin != "derived");
        saw_core |= origin == "core";
        saw_ontology_fact |= origin == "ontology_fact";
    }
    assert!(saw_core && saw_ontology_fact);
    let candidate: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&derivation).unwrap()).unwrap();
    assert_eq!(candidate["version"], 1);
    assert_eq!(candidate["production_bound"], document);
    let evidence = candidate["insertion_evidence"].as_array().unwrap();
    assert_eq!(evidence.len(), history.len());
    for (event, proof) in history.iter().zip(evidence) {
        let expected = if event["origin_hint"] == "derived" {
            "unproved"
        } else {
            "seed"
        };
        assert_eq!(proof["kind"], expected);
        assert_eq!(proof["prior_events"].as_array().unwrap().len(), 0);
        assert_eq!(proof["trace"].as_array().unwrap().len(), 0);
    }
    std::fs::remove_file(global).unwrap();
    std::fs::remove_file(bundle).unwrap();
    std::fs::remove_file(derivation).unwrap();
}

#[test]
fn provenance_schedule_preserves_the_uncertified_answer() {
    let input = br#"{"clauses":[{"body":[],"head":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}]}]}"#;
    let run = |required: bool, global: &std::path::Path, bundle: &std::path::Path| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"));
        if required {
            command
                .env("KM_CB_LEAN_REQUIRED", "1")
                .env("KM_CB_GLOBAL_MODEL_CERT", global)
                .env("KM_CB_LEAN_CERT_CHECKER", "/bin/true")
                .env("KM_CB_CERT_BUNDLE", bundle);
        }
        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                child.stdin.take().unwrap().write_all(input)?;
                child.wait_with_output()
            })
            .unwrap()
    };
    let global = snapshot_path("schedule-global");
    let bundle = snapshot_path("schedule-bundle");
    std::fs::write(&global, b"{}\n").unwrap();
    let ordinary = run(false, &global, &bundle);
    let certified_schedule = run(true, &global, &bundle);
    assert!(ordinary.status.success());
    assert!(certified_schedule.status.success());
    assert_eq!(certified_schedule.stdout, ordinary.stdout);
    std::fs::remove_file(global).unwrap();
    std::fs::remove_file(bundle).unwrap();
}
