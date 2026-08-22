use std::io::Write;
use std::process::{Command, Stdio};

const WIRE: &str = r#"{
  "concepts":["A","B"],
  "roles":[],
  "clauses":[],
  "queries":[0,1],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[],
  "transitive":[]
}"#;

const MIXED_WIRE: &str = r#"{
  "concepts":["A","B","Dormant"],
  "roles":[],
  "clauses":[{
    "body":[{"k":"c","neg":false,"c":2,"t":0},{"k":"eq","s":0,"t":0}],
    "head":[{"k":"c","neg":false,"c":0,"t":0}]
  }],
  "queries":[0,1],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[],
  "transitive":[]
}"#;

const ROLE_CHAIN_WIRE: &str = r#"{
  "concepts":["A","B","C","D"],
  "roles":["r0","r1","r2"],
  "clauses":[
    {"body":[{"k":"c","neg":false,"c":0,"t":0}],"head":[{"k":"e","r":0,"neg":false,"c":1,"t":0}]},
    {"body":[{"k":"c","neg":false,"c":1,"t":0}],"head":[{"k":"e","r":1,"neg":false,"c":3,"t":0}]},
    {"body":[{"k":"c","neg":false,"c":0,"t":0},{"k":"r","r":2,"s":0,"t":1}],"head":[{"k":"c","neg":false,"c":2,"t":1}]},
    {"body":[{"k":"c","neg":false,"c":3,"t":0}],"head":[{"k":"c","neg":true,"c":2,"t":0}]}
  ],
  "queries":[0,1,2,3],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[[0,1,2]],
  "transitive":[0]
}"#;

const CARDINALITY_SIDE_WIRE: &str = r#"{
  "concepts":["AtLeastTwo","Filler","Dormant"],
  "roles":["r"],
  "clauses":[{
    "body":[{"k":"c","neg":false,"c":2,"t":0},{"k":"eq","s":0,"t":0}],
    "head":[{"k":"c","neg":false,"c":1,"t":0}]
  }],
  "queries":[0,1],
  "inverse":false,
  "number":true,
  "nominals":[],
  "native_abox":{},
  "card_defs":[{"marker":0,"min":true,"n":2,"role":0,"filler":1}],
  "chains":[],
  "transitive":[]
}"#;

fn install_direct_projection_fixture(input: &mut serde_json::Value) {
    let concepts = input["concepts"].as_array().unwrap();
    let roles = input["roles"].as_array().unwrap();
    let mut target = input["clauses"].as_array().unwrap().clone();
    for chain in input["chains"].as_array().unwrap() {
        let chain = chain.as_array().unwrap();
        target.push(serde_json::json!({
            "body": [
                {"k":"r", "r":chain[0], "s":0, "t":1},
                {"k":"r", "r":chain[1], "s":1, "t":2}],
            "head": [{"k":"r", "r":chain[2], "s":0, "t":2}]
        }));
    }
    for role in input["transitive"].as_array().unwrap() {
        target.push(serde_json::json!({
            "body": [
                {"k":"r", "r":role, "s":0, "t":1},
                {"k":"r", "r":role, "s":1, "t":2}],
            "head": [{"k":"r", "r":role, "s":0, "t":2}]
        }));
    }
    let source: Vec<_> = target
        .iter()
        .map(|clause| {
            let atoms: Vec<_> = clause["body"]
                .as_array()
                .unwrap()
                .iter()
                .chain(clause["head"].as_array().unwrap())
                .collect();
            let max_variable = atoms
                .iter()
                .flat_map(|atom| match atom["k"].as_str().unwrap() {
                    "c" | "e" => vec![atom["t"].as_u64().unwrap() as usize],
                    "r" => vec![
                        atom["s"].as_u64().unwrap() as usize,
                        atom["t"].as_u64().unwrap() as usize,
                    ],
                    "eq" => vec![
                        atom["s"].as_u64().unwrap() as usize,
                        atom["t"].as_u64().unwrap() as usize,
                    ],
                    kind => panic!("unexpected HT atom {kind}"),
                })
                .max()
                .unwrap_or(0);
            let variable_names: Vec<_> = (0..=max_variable)
                .map(|variable| {
                    if variable == 0 {
                        "x".to_string()
                    } else {
                        format!("v{variable}")
                    }
                })
                .collect();
            let convert = |atom: &serde_json::Value| {
                let variable =
                    |field: &str| variable_names[atom[field].as_u64().unwrap() as usize].clone();
                match atom["k"].as_str().unwrap() {
                    "c" => serde_json::json!({"con": {
                        "concept": concepts[atom["c"].as_u64().unwrap() as usize],
                        "node": variable("t"),
                        "neg": atom["neg"]
                    }}),
                    "r" => serde_json::json!({"rol": {
                        "role": roles[atom["r"].as_u64().unwrap() as usize],
                        "source": variable("s"),
                        "target": variable("t")
                    }}),
                    "e" => serde_json::json!({"ex": {
                        "role": roles[atom["r"].as_u64().unwrap() as usize],
                        "filler": concepts[atom["c"].as_u64().unwrap() as usize],
                        "node": variable("t"),
                        "neg": atom["neg"]
                    }}),
                    "eq" => serde_json::json!({"equal": {
                        "left": variable("s"),
                        "right": variable("t")
                    }}),
                    kind => panic!("unexpected HT atom {kind}"),
                }
            };
            serde_json::json!({
                "variableNames": variable_names,
                "body": clause["body"].as_array().unwrap().iter().map(convert).collect::<Vec<_>>(),
                "head": clause["head"].as_array().unwrap().iter().map(convert).collect::<Vec<_>>()
            })
        })
        .collect();
    input["direct_projection_source"] = serde_json::Value::Array(source);
    if input["card_defs"]
        .as_array()
        .is_some_and(|definitions| !definitions.is_empty())
    {
        input["cardinality_projection_complete"] = serde_json::Value::Bool(true);
    }
}

fn run_with_input(
    input: &str,
    global_checker: &str,
    taxonomy_checker: &str,
    output_stem: &str,
) -> std::process::Output {
    let mut certified_input: serde_json::Value =
        serde_json::from_str(input).expect("test HT input is JSON");
    install_direct_projection_fixture(&mut certified_input);
    let certified_input = serde_json::to_vec(&certified_input).unwrap();
    let projection_checker = std::env::var("KM_HT_TEST_LEAN_PROJECTION_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let root = std::env::temp_dir().join(format!(
        "km-ht-taxonomy-runtime-{}-{output_stem}",
        std::process::id()
    ));
    let global_out = root.with_extension("global.json");
    let taxonomy_out = root.with_extension("taxonomy.json");
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        // Certification must select the exact source calculus even when the
        // ordinary performance route requests harvested consequences.
        .env("KM_HT_HARVEST", "1")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", projection_checker)
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CERT_CHECKER", global_checker)
        .env("KM_HT_LEAN_TAXONOMY_CERT_CHECKER", taxonomy_checker)
        .env("KM_HT_LEAN_CERT_OUT", &global_out)
        .env("KM_HT_LEAN_TAXONOMY_CERT_OUT", &taxonomy_out)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tableau worker");
    child
        .stdin
        .take()
        .expect("tableau stdin")
        .write_all(&certified_input)
        .expect("write tableau wire input");
    let output = child.wait_with_output().expect("wait for tableau worker");
    if output.status.success() {
        assert!(global_out.is_file(), "global certificate must be persisted");
        assert!(
            taxonomy_out.is_file(),
            "taxonomy certificate must be persisted"
        );
    }
    let _ = std::fs::remove_file(global_out);
    let _ = std::fs::remove_file(taxonomy_out);
    output
}

fn run(global_checker: &str, taxonomy_checker: &str, output_stem: &str) -> std::process::Output {
    run_with_input(WIRE, global_checker, taxonomy_checker, output_stem)
}

fn run_raw_certified(input: &str, projection_checker: Option<&str>) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tableau_cli"));
    command
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_CERT_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(checker) = projection_checker {
        command.env("KM_HT_LEAN_PROJECTION_CHECKER", checker);
    }
    let mut child = command.spawn().expect("spawn tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_certification_bypass_probe(
    extra_env: &[(&str, &str)],
    enable_ht: bool,
) -> std::process::Output {
    let mut input: serde_json::Value = serde_json::from_str(WIRE).unwrap();
    // Keep this probe focused on publication routing. A closed contradictory
    // source reaches terminal evidence without relying on the still-pending
    // blocked-open producer-refinement theorem.
    input["clauses"] = serde_json::json!([
        {"body":[], "head":[{"k":"c", "neg":false, "c":0, "t":0}]},
        {"body":[], "head":[{"k":"c", "neg":true, "c":0, "t":0}]}
    ]);
    install_direct_projection_fixture(&mut input);
    let mut command = Command::new(env!("CARGO_BIN_EXE_tableau_cli"));
    if enable_ht {
        command.env("KM_HT", "1").env("KM_HT_FORCE", "1");
    }
    command
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        // A branch that bypasses certification would incorrectly succeed.
        .env("KM_HT_LEAN_CERT_CHECKER", "/bin/false")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for &(name, value) in extra_env {
        command.env(name, value);
    }
    let mut child = command.spawn().expect("spawn tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_isolated_certification_interface(interface: &str) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tableau_cli"));
    command
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env(interface, "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().expect("spawn tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(WIRE.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_projection_only_certification() -> std::process::Output {
    let mut input: serde_json::Value = serde_json::from_str(WIRE).unwrap();
    install_direct_projection_fixture(&mut input);
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_native_abox_taxonomy_certification(
    source_taxonomy_checker: &str,
    joint_checker: Option<&str>,
) -> std::process::Output {
    let mut input: serde_json::Value = serde_json::from_str(WIRE).unwrap();
    input["nominals"] = serde_json::json!([0]);
    input["native_abox"] = serde_json::json!({
        "complete": true,
        "individuals": [{"proxies": [0], "assertions": []}],
        "different": [],
        "role_assertions": [],
        "negative_role_assertions": []
    });
    install_direct_projection_fixture(&mut input);

    let mut command = Command::new(env!("CARGO_BIN_EXE_tableau_cli"));
    command
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_DECISION_CHECKER", "/bin/true")
        .env(
            "KM_HT_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER",
            "/bin/true",
        )
        .env(
            "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER",
            "/bin/true",
        )
        .env(
            "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER",
            source_taxonomy_checker,
        )
        .env("KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_GLOBAL_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_EXECUTABLE_PUBLICATION_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(checker) = joint_checker {
        command.env(
            "KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER",
            checker,
        );
    }
    let mut child = command.spawn().expect("spawn tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_frontier_gated_certification(frontier_checker: &str) -> std::process::Output {
    let concepts: Vec<_> = (0..11).map(|index| format!("C{index}")).collect();
    let mut clauses = vec![serde_json::json!({
        "body": [],
        "head": [{"k":"c", "neg":false, "c":0, "t":0}]
    })];
    for index in 0..10 {
        clauses.push(serde_json::json!({
            "body": [{"k":"c", "neg":false, "c":index, "t":0}],
            "head": [{"k":"e", "r":0, "neg":false, "c":index + 1, "t":0}]
        }));
    }
    let mut input = serde_json::json!({
        "concepts": concepts,
        "roles": ["r"],
        "clauses": clauses,
        "queries": [0],
        "inverse": false,
        "number": false,
        "nominals": [],
        "native_abox": {},
        "card_defs": [],
        "chains": [],
        "transitive": []
    });
    install_direct_projection_fixture(&mut input);
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CERT_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", frontier_checker)
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn frontier-gated tableau worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn run_rejected_cyclic_fold_probe() -> std::process::Output {
    let mut input: serde_json::Value = serde_json::from_str(WIRE).unwrap();
    input["roles"] = serde_json::json!(["r"]);
    input["clauses"] = serde_json::json!([
        {"body":[], "head":[{"k":"c", "neg":false, "c":0, "t":0}]},
        {
            "body":[{"k":"c", "neg":false, "c":0, "t":0}],
            "head":[{"k":"e", "r":0, "neg":false, "c":0, "t":0}]
        }
    ]);
    install_direct_projection_fixture(&mut input);
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_UNSAT_NODES", "4")
        .env("KM_HT_LEAN_PROJECTION_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CERT_CHECKER", "/bin/false")
        .env("KM_HT_LEAN_FRONTIER_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        .env("KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER", "/bin/true")
        // This probe isolates finite progress under a fixed cap. Production
        // history has dedicated real-checker regressions in the library gate.
        .env("KM_HT_LEAN_PRODUCTION_TRACE_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn rejected cyclic-fold probe");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn certified_publication_requires_checker_and_source_projection() {
    let missing_checker = run_raw_certified(WIRE, None);
    assert!(!missing_checker.status.success());
    assert!(
        String::from_utf8_lossy(&missing_checker.stderr).contains("KM_HT_LEAN_PROJECTION_CHECKER")
    );

    let missing_source = run_raw_certified(WIRE, Some("/bin/true"));
    assert!(!missing_source.status.success());
    assert!(String::from_utf8_lossy(&missing_source.stderr)
        .contains("no proved source-to-HT projection"));
}

#[test]
fn every_iterative_frontier_is_checker_gated() {
    let rejected = run_frontier_gated_certification("/bin/false");
    assert!(!rejected.status.success());
    assert!(rejected.stdout.is_empty(), "unchecked frontier published output");
    assert!(
        String::from_utf8_lossy(&rejected.stderr)
            .contains("Lean rejected the regular decision frontier"),
        "{}",
        String::from_utf8_lossy(&rejected.stderr),
    );

    let accepted = run_frontier_gated_certification("/bin/true");
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr),
    );
}

#[test]
fn rejected_blocker_folds_make_finite_progress_at_one_budget() {
    let output = run_rejected_cyclic_fold_probe();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "rejected cyclic candidate published output");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("configured regular decision node cap"),
        "{stderr}",
    );
    assert!(!stderr.contains("overflowed usize"), "{stderr}");
}

#[test]
fn certified_publication_cannot_bypass_through_bridge_rules_or_legacy_tableau() {
    let bridge = run_certification_bypass_probe(&[("KM_HT_BRIDGE", "1")], true);
    assert!(!bridge.status.success());
    assert!(bridge.stdout.is_empty(), "rejected certificate published output");
    assert!(
        String::from_utf8_lossy(&bridge.stderr).contains("rejected the certificate"),
        "{}",
        String::from_utf8_lossy(&bridge.stderr),
    );

    let rules = run_certification_bypass_probe(&[("KM_RULES_CONSISTENCY", "1")], true);
    assert!(!rules.status.success());
    assert!(String::from_utf8_lossy(&rules.stderr).contains("rules-consistency"));

    let legacy = run_certification_bypass_probe(&[], false);
    assert!(!legacy.status.success());
    assert!(String::from_utf8_lossy(&legacy.stderr).contains("hypertableau mechanism"));
}

#[test]
fn isolated_native_taxonomy_interfaces_fail_closed() {
    for interface in [
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER",
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER",
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER",
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER",
        "KM_HT_LEAN_FRONTIER_CHECKER",
        "KM_HT_LEAN_DOUBLING_TRACE_CHECKER",
        "KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER",
        "KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER",
        "KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_ORDINARY_UNSAT_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_ROOTED_ORDINARY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_ROOTED_CARDINALITY_TAXONOMY_PRODUCTION_RUN_CHECKER",
        "KM_HT_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_RUN_MATRIX_CHECKER",
        "KM_HT_LEAN_NATIVE_ABOX_TAXONOMY_RUN_MATRIX_CHECKER",
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_GLOBAL_CHECKER",
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_GLOBAL_CHECKER",
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_TAXONOMY_CHECKER",
        "KM_HT_LEAN_SOURCE_BOUND_NATIVE_ABOX_CARDINALITY_TAXONOMY_CHECKER",
        "KM_HT_LEAN_EXECUTABLE_PUBLICATION_CHECKER",
        "KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER",
        "KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER",
    ] {
        let output = run_isolated_certification_interface(interface);
        assert!(!output.status.success(), "{interface} bypassed certification");
        assert!(output.stdout.is_empty(), "{interface} published unchecked output");
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("requires the global consistency route"),
            "{interface}: {}",
            String::from_utf8_lossy(&output.stderr),
        );
    }
}

#[test]
fn native_abox_taxonomy_requires_the_joint_source_classification_checker() {
    let output = run_native_abox_taxonomy_certification("/bin/true", None);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "unchecked taxonomy was published");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("KM_HT_LEAN_NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER"),
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn native_abox_taxonomy_is_gated_by_the_joint_checker() {
    let rejected = run_native_abox_taxonomy_certification("/bin/true", Some("/bin/false"));
    assert!(!rejected.status.success());
    assert!(
        rejected.stdout.is_empty(),
        "unchecked taxonomy was published"
    );
    assert!(
        String::from_utf8_lossy(&rejected.stderr)
            .contains("native-abox-joint-source-classification"),
        "{}",
        String::from_utf8_lossy(&rejected.stderr),
    );

    let accepted = run_native_abox_taxonomy_certification("/bin/true", Some("/bin/true"));
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr),
    );
    let classification: serde_json::Value =
        serde_json::from_slice(&accepted.stdout).expect("classification is JSON");
    assert_eq!(classification["consistent"], true);
}

#[test]
fn joint_checker_does_not_replace_the_source_taxonomy_checker() {
    let output = run_native_abox_taxonomy_certification("/bin/false", Some("/bin/true"));
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "unchecked taxonomy was published");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("native-abox-taxonomy-source"),
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn projection_check_alone_cannot_publish_an_unchecked_global_verdict() {
    let output = run_projection_only_certification();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "unchecked global verdict was published");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("requires KM_HT_LEAN_CERT_CHECKER"),
        "{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn accepted_complete_taxonomy_is_the_published_classification() {
    let global_checker =
        std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER").unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run(&global_checker, &taxonomy_checker, "accept");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert_eq!(value["unsatisfiable"], serde_json::json!([]));
    assert_eq!(
        value["subsumptions"],
        serde_json::json!([["A", "A"], ["B", "B"]])
    );
}

#[test]
fn rejecting_taxonomy_checker_suppresses_publication() {
    let output = run("/bin/true", "/bin/false", "reject");
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "unchecked classification was published"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("rejected the certificate"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn accepted_mixed_taxonomy_is_read_from_wrapped_evidence() {
    let global_checker =
        std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER").unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run_with_input(
        MIXED_WIRE,
        &global_checker,
        &taxonomy_checker,
        "mixed-accept",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert_eq!(value["unsatisfiable"], serde_json::json!([]));
    assert_eq!(
        value["subsumptions"],
        serde_json::json!([["A", "A"], ["B", "B"]])
    );
}

#[test]
fn certified_taxonomy_restores_and_checks_raw_role_chain_axioms() {
    let global_checker = std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER")
        .or_else(|_| std::env::var("KM_HT_TEST_LEAN_CHECKER"))
        .unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run_with_input(
        ROLE_CHAIN_WIRE,
        &global_checker,
        &taxonomy_checker,
        "raw-role-chain",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert!(value["unsatisfiable"]
        .as_array()
        .expect("unsatisfiable array")
        .contains(&serde_json::json!("A")));
}

#[test]
fn first_class_cardinality_global_result_is_checker_gated() {
    let checker = std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER")
        .or_else(|_| std::env::var("KM_HT_TEST_LEAN_CHECKER"))
        .unwrap_or_else(|_| "/bin/true".to_string());
    let mut input: serde_json::Value = serde_json::from_str(CARDINALITY_SIDE_WIRE).unwrap();
    install_direct_projection_fixture(&mut input);
    let input = serde_json::to_vec(&input).unwrap();
    let projection_checker = std::env::var("KM_HT_TEST_LEAN_PROJECTION_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_CERT_CHECKER", checker)
        .env("KM_HT_LEAN_PROJECTION_CHECKER", projection_checker)
        .env("KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tableau worker");
    child
        .stdin
        .take()
        .expect("tableau stdin")
        .write_all(&input)
        .expect("write cardinality wire input");
    let output = child.wait_with_output().expect("wait for tableau worker");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
}

#[test]
fn first_class_cardinality_taxonomy_is_checker_gated() {
    let global_checker = std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER")
        .or_else(|_| std::env::var("KM_HT_TEST_LEAN_CHECKER"))
        .unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run_with_input(
        CARDINALITY_SIDE_WIRE,
        &global_checker,
        &taxonomy_checker,
        "cardinality-taxonomy",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert_eq!(value["unsatisfiable"], serde_json::json!([]));
}
