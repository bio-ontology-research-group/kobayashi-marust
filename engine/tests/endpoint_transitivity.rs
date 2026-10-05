use std::process::Command;

#[test]
fn endpoint_transitivity_projection_retains_observable_chain_constraints() {
    let directory = std::env::temp_dir().join(format!("km-endpoint-transitivity-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let base = "Ontology(Declaration(Class(<urn:A>)) Declaration(Class(<urn:B>)) Declaration(Class(<urn:C>)) Declaration(Class(<urn:D>)) Declaration(ObjectProperty(<urn:r>)) Declaration(ObjectProperty(<urn:s>)) Declaration(ObjectProperty(<urn:t>)) TransitiveObjectProperty(<urn:r>) ObjectPropertyDomain(<urn:r> <urn:A>) ObjectPropertyRange(<urn:r> <urn:B>) ObjectPropertyAssertion(<urn:r> <urn:a> <urn:b>) ObjectPropertyAssertion(<urn:r> <urn:b> <urn:c>) EXTRA)";
    for (name, extra, keep) in [
        ("endpoint_only", "", false),
        ("absorbing", "SubObjectPropertyOf(ObjectPropertyChain(<urn:r> <urn:s>) <urn:s>)", false),
        ("nonabsorbing", "SubObjectPropertyOf(ObjectPropertyChain(<urn:r> <urn:s>) <urn:t>)", true),
        ("guarded", "SubClassOf(ObjectSomeValuesFrom(<urn:r> <urn:C>) <urn:D>) ClassAssertion(<urn:C> <urn:c>) ClassAssertion(ObjectComplementOf(<urn:D>) <urn:a>)", false),
        ("inverse_endpoints", "InverseObjectProperties(<urn:r> <urn:s>) ObjectPropertyDomain(<urn:s> <urn:C>)", false),
        ("inverse_negative", "InverseObjectProperties(<urn:r> <urn:s>) NegativeObjectPropertyAssertion(<urn:s> <urn:c> <urn:a>)", true),
        ("super_universal", "SubObjectPropertyOf(<urn:r> <urn:s>) SubClassOf(<urn:A> ObjectAllValuesFrom(<urn:s> <urn:C>))", true),
        ("negative", "NegativeObjectPropertyAssertion(<urn:r> <urn:a> <urn:c>)", true),
        ("universal", "SubClassOf(<urn:A> ObjectAllValuesFrom(<urn:r> <urn:C>))", true),
        ("rule", "DLSafeRule(Body(ObjectPropertyAtom(<urn:r> Variable(<urn:x>) Variable(<urn:y>))) Head(ObjectPropertyAtom(<urn:s> Variable(<urn:x>) Variable(<urn:y>))))", true),
    ] {
        let path = directory.join(format!("{name}.ofn"));
        std::fs::write(&path, base.replace("EXTRA", extra)).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_km")).env("KM_NOMINALS", "1")
            .args(["ofn"]).arg(&path).output().unwrap();
        assert!(out.status.success(), "{name}: {}", String::from_utf8_lossy(&out.stderr));
        let input: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        let raw_chain = input["clauses"].as_array().unwrap().iter().any(|clause| {
            let body = clause["body"].as_array().unwrap();
            let head = clause["head"].as_array().unwrap();
            body.len() == 2 && head.len() == 1 && body.iter().chain(head)
                .all(|atom| atom["kind"] == "role" && atom["role"] == body[0]["role"])
        });
        assert_eq!(raw_chain, keep, "{name}: semantic consumers must control projection");
        for clause in input["clauses"].as_array().unwrap() {
            let body = clause["body"].as_array().unwrap();
            let head = clause["head"].as_array().unwrap();
            if body.len() == 2 && head.len() == 1 && body.iter().chain(head)
                .all(|atom| atom["kind"] == "role" && atom["role"] == body[0]["role"])
            {
                assert!(body.iter().all(|atom|
                    atom["source"] == serde_json::json!({"kind":"var", "name":"x"})
                    || atom["target"] == serde_json::json!({"kind":"var", "name":"x"})),
                    "{name}: retained transitivity must be centered on its shared variable for the CB loader");
            }
        }
        if name == "guarded" {
            let answer = Command::new(env!("CARGO_BIN_EXE_km"))
                .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
            assert!(answer.status.success(), "{}", String::from_utf8_lossy(&answer.stderr));
            let answer: serde_json::Value = serde_json::from_slice(&answer.stdout).unwrap();
            assert_eq!(answer["consistent"], false, "chain entailment must still cause the clash");
            assert_eq!(answer["dropped"], 0);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
