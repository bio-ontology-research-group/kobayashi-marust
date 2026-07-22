use std::process::Command;

#[test]
fn cli_returns_source_axiom_justification_for_named_subsumption() {
    let ontology = std::env::temp_dir().join(format!(
        "km-explain-cli-{}-named-subsumption.ofn",
        std::process::id()
    ));
    std::fs::write(
        &ontology,
        r#"Ontology(
SubClassOf(<http://example.org/A> <http://example.org/B>)
SubClassOf(<http://example.org/B> <http://example.org/C>)
SubClassOf(<http://example.org/Noise> <http://example.org/C>)
)"#,
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args([
            "explain",
            "--route",
            "auto",
            "--max-axioms",
            "8",
            "--max-checks",
            "9",
            ontology.to_str().unwrap(),
            "subclass",
            "http://example.org/A",
            "http://example.org/C",
        ])
        .env("KM_THREADS", "1")
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&ontology);

    assert!(
        output.status.success(),
        "km explain failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["schemaVersion"], 1);
    assert_eq!(report["status"], "entailed");
    assert_eq!(report["oracleSubsetMinimal"], true);
    assert_eq!(report["limitReached"], false);
    assert_eq!(report["sourceAxiomCount"], 3);
    assert_eq!(report["justifications"][0]["axiomCount"], 2);
    let axioms: Vec<&str> = report["justifications"][0]["axioms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|axiom| axiom["functionalSyntax"].as_str().unwrap())
        .collect();
    assert!(axioms.contains(&"SubClassOf(<http://example.org/A> <http://example.org/B>)"));
    assert!(axioms.contains(&"SubClassOf(<http://example.org/B> <http://example.org/C>)"));
    assert!(!axioms.iter().any(|axiom| axiom.contains("Noise")));
}
