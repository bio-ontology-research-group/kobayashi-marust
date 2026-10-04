use std::process::Command;

#[test]
fn source_clash_precedes_rule_admission_but_consistent_source_still_declines() {
    let base = r#"Prefix(:=<http://km.test/>)
        Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>) Ontology(
        Declaration(Class(:Key)) Declaration(Class(:NonKey))
        Declaration(Class(:NonPrimary)) Declaration(Class(:Primary))
        Declaration(Class(:Attribute)) Declaration(Class(:Unknown))
        Declaration(Class(:UnknownResult)) Declaration(DataProperty(:p))
        DisjointClasses(:Key :NonKey)
        EquivalentClasses(:NonPrimary ObjectUnionOf(
            ObjectIntersectionOf(ObjectComplementOf(:Primary) :Attribute) :NonKey))
        SubClassOf(:NonPrimary :Key)
        ClassAssertion(:Unknown :salary)
        DataPropertyAssertion(:p :salary "opaque"^^xsd:string)
        DLSafeRule(Body(ClassAtom(:Unknown Variable(:x))
            BuiltInAtom(<urn:unsupported:builtin> Variable(:x)))
            Head(ClassAtom(:UnknownResult Variable(:x))))
    "#;
    for (case, assertion, clash) in [
        ("clash", "ClassAssertion(:NonKey :salary)", true),
        ("no-witness", "", false),
        ("unrelated-witness", "ClassAssertion(:Attribute :salary)", false),
    ] {
        let path = std::env::temp_dir().join(format!("km-source-clash-{}-{case}.ofn", std::process::id()));
        std::fs::write(&path, format!("{base}{assertion})")).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
        std::fs::remove_file(path).unwrap();
        if clash {
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
            let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(result["consistent"], false);
            assert_eq!(result["dropped"], 0);
        } else {
            assert_eq!(output.status.code(), Some(3), "{case}: {}", String::from_utf8_lossy(&output.stdout));
        }
    }
}

#[test]
fn invalid_literal_is_refused_even_when_source_has_an_independent_clash() {
    for clash in [false, true] {
        let assertion = if clash { "ClassAssertion(owl:Nothing <urn:a>)" } else { "" };
        let source = format!(r#"Ontology(
            Declaration(DataProperty(<urn:p>))
            DataPropertyAssertion(<urn:p> <urn:a> "opaque"^^rdfs:Literal)
            {assertion})"#);
        let path = std::env::temp_dir().join(format!("km-invalid-clash-{}-{clash}.ofn", std::process::id()));
        std::fs::write(&path, &source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
        std::fs::remove_file(path).unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(error.contains("rdfs:Literal") && error.contains("no lexical space"), "{error}");
    }
}
