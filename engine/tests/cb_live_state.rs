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
    assert_eq!(snapshot["version"], 2);
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
