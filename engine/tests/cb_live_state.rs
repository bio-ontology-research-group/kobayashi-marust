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

fn write_trivial_typed_source(path: &std::path::Path) {
    let x = serde_json::json!({"var": {"index": 0}});
    let concept = serde_json::json!({"predicate": {"predicate": {"concept": {
        "concept": 0, "term": x
    }}}});
    let source = serde_json::json!({"source": {
        "version": 1,
        "concept_count": 1,
        "role_count": 0,
        "function_count": 0,
        "individual_count": 1,
        "source_clauses": [{"gci": {"body": [], "head": [0]}}],
        "role_chains": [],
        "role_axioms": [],
        "ontology": [{"body": [], "head": [concept]}]
    }});
    std::fs::write(path, serde_json::to_vec(&source).unwrap()).unwrap();
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
    assert_eq!(snapshot["version"], 5);
    assert!(snapshot["concept_count"].is_number());
    assert_eq!(
        snapshot["concept_names"].as_array().unwrap().len(),
        snapshot["concept_count"].as_u64().unwrap() as usize
    );
    assert!(snapshot["role_count"].is_number());
    assert!(snapshot["function_count"].is_number());
    assert!(snapshot["source_individual_count"].is_number());
    assert!(snapshot["runtime_individual_count"].is_number());
    assert!(snapshot["source_ontology"].is_array());
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
        assert!(context["nominal_ground"].is_boolean());
        assert!(context["query_concept"].is_null() || context["query_concept"].is_number());
        assert!(context["core"].is_array());
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
    assert!(String::from_utf8_lossy(&output.stderr).contains("KM_CB_LEAN_CERT_CHECKER"));
}

#[test]
fn production_certification_rejects_an_external_source_file() {
    let global = snapshot_path("external-source-rejected");
    let bundle = snapshot_path("external-source-bundle");
    std::fs::write(&global, b"{}\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_GLOBAL_MODEL_CERT", &global)
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/false")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env_remove("KM_CB_TEST_ALLOW_EXTERNAL_SOURCE")
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
    assert!(String::from_utf8_lossy(&output.stderr).contains("in-band cb_typed_source"));
    assert!(!bundle.exists());
    std::fs::remove_file(global).unwrap();
}

#[test]
fn in_band_source_reaches_the_checker_boundary() {
    let bundle = snapshot_path("in-band-source-bundle");
    let input = r#"{"clauses":[],"cb_typed_source":{}}"#;
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/false")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env_remove("KM_CB_TEST_ALLOW_EXTERNAL_SOURCE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            child.stdin.take().unwrap().write_all(input.as_bytes())?;
            child.wait_with_output()
        })
        .unwrap();
    assert_eq!(output.status.code(), Some(5));
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("Lean checker rejected"));
    assert!(bundle.exists());
    std::fs::remove_file(bundle).unwrap();
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
                br#"{"clauses":[{"body":[],"head":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}]},{"body":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}],"head":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}]}]}"#,
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
    assert!(document["concept_names"].is_array());
    assert!(document["public_rows"].is_array());
    assert!(document["public_subsumptions"].is_array());
    assert!(document["unsatisfiable"].is_array());
    assert!(document["inconsistent"].is_boolean());
    assert!(document["inconsistency_witness"].is_null()
        || document["inconsistency_witness"].is_object());
    let derivation_document = &document["derivation"];
    assert_eq!(derivation_document["version"], 2);
    let production_bound = &derivation_document["production_bound"];
    assert_eq!(production_bound["version"], 1);
    let live_state = &production_bound["live_state"];
    assert_eq!(live_state["version"], 5);
    assert!(live_state["concept_count"].is_number());
    assert_eq!(
        live_state["concept_names"].as_array().unwrap().len(),
        live_state["concept_count"].as_u64().unwrap() as usize
    );
    assert!(live_state["role_count"].is_number());
    assert!(live_state["function_count"].is_number());
    assert!(live_state["source_individual_count"].is_number());
    assert!(live_state["runtime_individual_count"].is_number());
    assert!(live_state["source_ontology"].is_array());
    for context in live_state["contexts"].as_array().unwrap() {
        assert!(context["nominal_ground"].is_boolean());
        assert!(context["query_concept"].is_null() || context["query_concept"].is_number());
        assert!(context["core"].is_array());
    }
    let history = live_state["insertion_history"]
        .as_array()
        .unwrap();
    assert!(!history.is_empty());
    let mut saw_core = false;
    let mut saw_ontology_fact = false;
    let mut saw_hyper = false;
    for (sequence, event) in history.iter().enumerate() {
        assert_eq!(event["sequence"], sequence);
        let root = event["root"].as_bool().unwrap();
        let arena = if root {
            &live_state["root_clause_arena"]
        } else {
            &live_state["ordinary_clause_arena"]
        };
        assert!(event["clause_id"].as_u64().unwrap() < arena.as_array().unwrap().len() as u64);
        let origin = event["origin_hint"].as_str().unwrap();
        assert!(matches!(origin, "core" | "ontology_fact" | "derived"));
        assert_eq!(event["origin_index"].is_number(), origin != "derived");
        saw_core |= origin == "core";
        saw_ontology_fact |= origin == "ontology_fact";
        if origin == "derived" && event["rule_hint"] == "hyper" {
            saw_hyper = true;
            let evidence = &event["rule_evidence"];
            assert_eq!(evidence["kind"], "hyper");
            assert!(evidence["ontology_index"].as_u64().unwrap()
                < live_state["source_ontology"]
                    .as_array()
                    .unwrap()
                    .len() as u64);
            let premises = evidence["context_clause_ids"].as_array().unwrap();
            let matched = evidence["matched_predicates"].as_array().unwrap();
            assert_eq!(premises.len(), matched.len());
            assert!(!premises.is_empty());
            for premise in premises {
                let premise_id = premise.as_u64().unwrap();
                assert!(history[..sequence].iter().any(|prior| {
                    prior["context_index"] == event["context_index"]
                        && prior["root"] == event["root"]
                        && prior["clause_id"].as_u64() == Some(premise_id)
                }));
            }
            assert!(evidence["substitution"].is_array());
        }
    }
    assert!(saw_core && saw_ontology_fact);
    assert!(saw_hyper);
    let candidate: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&derivation).unwrap()).unwrap();
    assert_eq!(candidate, document);
    let evidence = derivation_document["insertion_evidence"]
        .as_array()
        .unwrap();
    assert_eq!(evidence.len(), history.len());
    for (event, proof) in history.iter().zip(evidence) {
        let expected = if event["rule_hint"] == "hyper" {
            "local"
        } else if event["origin_hint"] == "derived" {
            "unproved"
        } else {
            "seed"
        };
        assert_eq!(proof["kind"], expected);
        if expected == "local" {
            assert!(!proof["prior_events"].as_array().unwrap().is_empty());
            assert!(!proof["trace"].as_array().unwrap().is_empty());
        } else {
            assert_eq!(proof["prior_events"].as_array().unwrap().len(), 0);
            assert_eq!(proof["trace"].as_array().unwrap().len(), 0);
        }
        assert_eq!(proof["discarded"].as_array().unwrap().len(), 0);
    }
    std::fs::remove_file(global).unwrap();
    std::fs::remove_file(bundle).unwrap();
    std::fs::remove_file(derivation).unwrap();
}

#[test]
fn exact_lean_mode_requires_a_candidate_path() {
    let global = snapshot_path("exact-config-global");
    let bundle = snapshot_path("exact-config-bundle");
    std::fs::write(&global, b"{}\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_GLOBAL_MODEL_CERT", &global)
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/true")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env("KM_CB_EXACT_LEAN_CERT_CHECKER", "/bin/true")
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
    assert!(String::from_utf8_lossy(&output.stderr)
        .contains("KM_CB_EXACT_TAXONOMY_CANDIDATE is required"));
    assert!(!bundle.exists());
    std::fs::remove_file(global).unwrap();
}

#[test]
fn exact_lean_rejection_prevents_publication() {
    let global = snapshot_path("exact-reject-global");
    let bundle = snapshot_path("exact-reject-bundle");
    let exact = snapshot_path("exact-reject-candidate");
    write_trivial_typed_source(&global);
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_GLOBAL_MODEL_CERT", &global)
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/true")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env("KM_CB_EXACT_TAXONOMY_CANDIDATE", &exact)
        .env("KM_CB_EXACT_LEAN_CERT_CHECKER", "/bin/false")
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
    assert!(String::from_utf8_lossy(&output.stderr).contains("exact CB Lean checker rejected"));
    assert!(bundle.exists());
    assert!(exact.exists());
    std::fs::remove_file(global).unwrap();
    std::fs::remove_file(bundle).unwrap();
    std::fs::remove_file(exact).unwrap();
}

#[test]
fn both_lean_checkers_must_accept_before_publication() {
    let global = snapshot_path("exact-accept-global");
    let bundle = snapshot_path("exact-accept-bundle");
    let exact = snapshot_path("exact-accept-candidate");
    write_trivial_typed_source(&global);
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_GLOBAL_MODEL_CERT", &global)
        .env("KM_CB_LEAN_CERT_CHECKER", "/bin/true")
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env("KM_CB_EXACT_TAXONOMY_CANDIDATE", &exact)
        .env("KM_CB_EXACT_LEAN_CERT_CHECKER", "/bin/true")
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
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output.stdout.is_empty());
    let matrix: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&exact).unwrap()).unwrap();
    assert_eq!(matrix["version"], 1);
    assert_eq!(matrix["cells"].as_array().unwrap().len(), 1);
    assert_eq!(matrix["cells"][0]["evidence"], "reflexive");
    std::fs::remove_file(global).unwrap();
    std::fs::remove_file(bundle).unwrap();
    std::fs::remove_file(exact).unwrap();
}

#[test]
fn source_exact_lean_checker_accepts_real_cb_publication() {
    let checker = std::env::var_os("KM_CB_TEST_SOURCE_EXACT_TAXONOMY_CHECKER")
        .expect("the integration gate must provide the real source-exact Lean checker");
    let source = snapshot_path("source-exact-typed-source");
    let bundle = snapshot_path("source-exact-live-bundle");
    let exact = snapshot_path("source-exact-matrix");
    let x = serde_json::json!({"var": {"index": 0}});
    let concept = |id| serde_json::json!({"predicate": {"predicate": {"concept": {
        "concept": id, "term": x
    }}}});
    std::fs::write(
        &source,
        serde_json::to_vec(&serde_json::json!({
            "version": 1,
            "concept_count": 2,
            "role_count": 0,
            "function_count": 0,
            "individual_count": 1,
            "source_clauses": [{"gci": {"body": [0], "head": [1]}}],
            "role_chains": [],
            "role_axioms": [],
            "ontology": [{"body": [concept(0)], "head": [concept(1)]}]
        }))
        .unwrap(),
    )
    .unwrap();
    let input = br#"{"clauses":[{"body":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}],"head":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}]}]}"#;
    let output = Command::new(env!("CARGO_BIN_EXE_kobayashi-marust"))
        .env("KM_CB_LEAN_REQUIRED", "1")
        .env("KM_CB_TYPED_SOURCE_CERT", &source)
        .env("KM_CB_CERT_BUNDLE", &bundle)
        .env("KM_CB_SOURCE_EXACT_TAXONOMY_CANDIDATE", &exact)
        .env("KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER", checker)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            child.stdin.take().unwrap().write_all(input)?;
            child.wait_with_output()
        })
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!output.stdout.is_empty());
    let candidate: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&exact).unwrap()).unwrap();
    assert_eq!(candidate["source"]["source_clauses"][0]["gci"]["body"], serde_json::json!([0]));
    assert_eq!(candidate["taxonomy"]["published"], serde_json::json!([true, true, false, true]));
    std::fs::remove_file(source).unwrap();
    std::fs::remove_file(bundle).unwrap();
    std::fs::remove_file(exact).unwrap();
}

#[test]
fn provenance_schedule_preserves_the_uncertified_answer() {
    // Exercise the two query optimizations deliberately bypassed by certified
    // mode: A/B form a unit-equivalence SCC and C is promoted to bottom.
    let input = br#"{"clauses":[{"body":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}],"head":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}]},{"body":[{"kind":"concept","concept":"B","term":{"kind":"var","name":"x"}}],"head":[{"kind":"concept","concept":"A","term":{"kind":"var","name":"x"}}]},{"body":[{"kind":"concept","concept":"C","term":{"kind":"var","name":"x"}}],"head":[]}]}"#;
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
