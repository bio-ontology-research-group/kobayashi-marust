use std::process::{Command, Output};

fn run(name: &str, source: &str, options: &[&str], environment: Option<&str>) -> Output {
    let path = std::env::temp_dir().join(format!("km-graph-json-{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") { command.env_remove(key); }
    }
    command.env("KM_THREADS", "1").arg("classify").args(options).arg(&path);
    if let Some(value) = environment { command.env("KM_JSON_GRAPH_EDGES", value); }
    let result = command.output().unwrap();
    std::fs::remove_file(path).unwrap();
    result
}

const SOURCE: &str = "Ontology(Declaration(Class(<urn:A>)) Declaration(Class(<urn:B>)) Declaration(Class(<urn:C>)) SubClassOf(<urn:A> <urn:B>) SubClassOf(<urn:B> <urn:C>))";

#[test]
fn explicit_graph_json_and_environment_option_preserve_small_route_answers() {
    let normal = run("options", SOURCE, &[], None);
    assert!(normal.status.success());
    let expected: serde_json::Value = serde_json::from_slice(&normal.stdout).unwrap();
    assert!(expected.get("subsumptions_are_graph_edges").is_none());
    for (options, env) in [(&["--json-edges"][..], None), (&[][..], Some("1"))] {
        let output = run("options", SOURCE, options, env);
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let mut actual: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(actual.as_object_mut().unwrap().remove("subsumptions_are_graph_edges"), Some(true.into()));
        assert_eq!(actual, expected);
    }
    let disabled = run("options", SOURCE, &[], Some("0"));
    assert_eq!(disabled.stdout, normal.stdout);
}

#[test]
fn graph_json_does_not_bypass_invalid_literal_refusal() {
    let source = "Ontology(Declaration(DataProperty(<urn:p>)) Declaration(NamedIndividual(<urn:i>)) DataPropertyAssertion(<urn:p> <urn:i> \"bad\"^^<http://www.w3.org/2000/01/rdf-schema#Literal>))";
    let before = run("invalid", source, &[], None);
    let after = run("invalid", source, &["--json-edges"], None);
    assert_eq!(before.status.code(), Some(2));
    assert_eq!(before.status.code(), after.status.code());
    assert!(before.stdout.is_empty() && after.stdout.is_empty());
    assert_eq!(before.stderr, after.stderr);
}

#[test]
fn graph_json_rejects_conflicting_line_output() {
    for (options, env) in [(&["--lines", "--json-edges"][..], None), (&["--lines"][..], Some("1"))] {
        let output = run("conflict", SOURCE, options, env);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("cannot be combined"));
    }
}
