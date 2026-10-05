use std::process::Command;

#[test]
fn grounded_rules_preserve_equality_role_heads_and_empty_heads() {
    let cases = [
        ("same-head", r#"ClassAssertion(:B :b)
          DLSafeRule(Body(ClassAtom(:C Variable(:x)))
            Head(SameIndividualAtom(Variable(:x) :b)))"#, "B", false),
        ("different-head", r#"DLSafeRule(Body(ClassAtom(:C Variable(:x)))
            Head(DifferentIndividualsAtom(Variable(:x) :a)))"#, "B", true),
        ("role-head", r#"ClassAssertion(:B :b)
          SubClassOf(ObjectSomeValuesFrom(:r :B) :D)
          DLSafeRule(Body(ClassAtom(:C Variable(:x)))
            Head(ObjectPropertyAtom(:r Variable(:x) :b)))"#, "D", false),
        ("empty-head", r#"DLSafeRule(Body(ClassAtom(:C Variable(:x))) Head())"#, "B", true),
        ("conjunctive-head", r#"DLSafeRule(Body(ClassAtom(:C Variable(:x)))
            Head(ClassAtom(:B Variable(:x)) ClassAtom(:D Variable(:x))))"#, "D", false),
    ];
    for (case, axioms, superclass, unsatisfiable) in cases {
        let source = format!(r#"Prefix(:=<http://km.test/>) Ontology(
          Declaration(Class(:C)) Declaration(Class(:B)) Declaration(Class(:D))
          Declaration(ObjectProperty(:r))
          Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
          SubClassOf(:C ObjectOneOf(:a)) {axioms})"#);
        let path = std::env::temp_dir().join(format!("km-ground-shape-{}-{case}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_km"))
            .env("KM_GROUND_RULE_SOURCE", "1")
            .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
        std::fs::remove_file(path).unwrap();
        assert!(out.status.success(), "{case}: {}", String::from_utf8_lossy(&out.stderr));
        let result: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(result["consistent"], true, "{case}: {result}");
        assert_eq!(result["dropped"], 0, "{case}: {result}");
        if unsatisfiable {
            assert!(result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!(":C")), "{case}: {result}");
        } else {
            assert!(result["subsumptions"].as_array().unwrap().contains(
                &serde_json::json!([":C", format!(":{superclass}")])), "{case}: {result}");
        }
    }
}

#[test]
fn nominal_query_reactivates_cached_abox_constraints() {
    // C identifies b. The asserted r(a,b) and universal on a therefore
    // entail C <= Bad, independently of the unrelated restriction defining D.
    // Cardinality/datatype metadata selects the retained native ABox schedule.
    for (case, restriction) in [
        ("datatype", "DataHasValue(<http://km.test/p> \"NULL\"^^xsd:string)"),
        ("cardinality", "ObjectMaxCardinality(1 <http://km.test/p> owl:Thing)"),
    ] {
        let property_kind = if case == "datatype" { "DataProperty" } else { "ObjectProperty" };
        let source = format!(r#"Ontology(
          Declaration(ObjectProperty(<http://km.test/r>))
          Declaration({property_kind}(<http://km.test/p>))
          Declaration(Class(<http://km.test/C>))
          Declaration(Class(<http://km.test/Bad>))
          Declaration(Class(<http://km.test/D>))
          Declaration(NamedIndividual(<http://km.test/a>))
          Declaration(NamedIndividual(<http://km.test/b>))
          SubClassOf(<http://km.test/C> ObjectOneOf(<http://km.test/b>))
          ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
          ClassAssertion(ObjectAllValuesFrom(<http://km.test/r>
            ObjectUnionOf(ObjectComplementOf(<http://km.test/C>) <http://km.test/Bad>))
            <http://km.test/a>)
          EquivalentClasses(<http://km.test/D> {restriction})
          ClassAssertion(<http://km.test/D> <http://km.test/a>))"#);
        let path = std::env::temp_dir().join(format!(
            "km-nominal-query-cache-{}-{case}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_km"))
            .env("KM_MECHANISM", "ht").env("KM_HT_ONLY", "certified")
            .env("KM_NOMINALS", "1").env("KM_TRIGGER_ABSORB", "1")
            .env("KM_NO_INPROC_ENGINE", "1")
            .env_remove("KM_GROUND_RULE_SOURCE")
            .env_remove("KM_BRIDGE_FRESH_ENV")
            .env_remove("KM_BRIDGE_NO_RETAINED_BASE")
            .env_remove("KM_BRIDGE_NO_REPRESENTATIVE_CACHE")
            .args(["classify", "--route", "manual"]).arg(&path).output().unwrap();
        std::fs::remove_file(path).unwrap();
        assert!(out.status.success(), "{case}: {}", String::from_utf8_lossy(&out.stderr));
        let result: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(result["consistent"], true);
        assert_eq!(result["dropped"], 0);
        assert!(result["subsumptions"].as_array().unwrap().contains(
            &serde_json::json!(["http://km.test/C", "http://km.test/Bad"])),
            "{case}: {result}");
    }
}

#[test]
fn grounded_constant_rule_uses_query_premise_and_preserves_original_file() {
    let source=r#"Ontology(
      Declaration(Class(<http://km.test/C>)) Declaration(Class(<http://km.test/Bad>))
      Declaration(ObjectProperty(<http://km.test/r>)) Declaration(DataProperty(<http://km.test/p>))
      SubClassOf(<http://km.test/C> ObjectOneOf(<http://km.test/b>))
      ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
      DataPropertyAssertion(<http://km.test/p> <http://km.test/a> "NULL"^^xsd:string)
      DLSafeRule(Body(ClassAtom(<http://km.test/C> Variable(<http://km.test/y>))
        ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/y>))
        DataPropertyAtom(<http://km.test/p> Variable(<http://km.test/x>) "NULL"^^xsd:string))
        Head(ClassAtom(<http://km.test/Bad> Variable(<http://km.test/y>)))))"#;
    let path=std::env::temp_dir().join(format!("km-ground-rule-source-{}.ofn",std::process::id()));
    std::fs::write(&path,source).unwrap();
    let out=Command::new(env!("CARGO_BIN_EXE_km")).env("KM_GROUND_RULE_SOURCE","1")
        .args(["classify","--route","auto"]).arg(&path).output().unwrap();
    assert_eq!(std::fs::read_to_string(&path).unwrap(),source);
    std::fs::remove_file(path).unwrap();
    assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
    let result:serde_json::Value=serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(result["consistent"],true); assert_eq!(result["dropped"],0);
    assert!(!result.to_string().contains("urn:km:ground-rule#"),"private classes leaked: {result}");
    assert!(result["subsumptions"].as_array().unwrap().contains(
        &serde_json::json!(["http://km.test/C","http://km.test/Bad"])),"{result}");
}

#[test]
fn grounded_object_rule_query_reads_native_compact_taxonomy() {
    let source=r#"Ontology(
      Declaration(ObjectProperty(<http://km.test/r>))
      Declaration(Class(<http://km.test/C>)) Declaration(Class(<http://km.test/Bad>))
      SubClassOf(<http://km.test/C> ObjectOneOf(<http://km.test/b>))
      ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
      DLSafeRule(Body(ClassAtom(<http://km.test/C> Variable(<http://km.test/y>))
        ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/y>)))
        Head(ClassAtom(<http://km.test/Bad> Variable(<http://km.test/y>)))))"#;
    let path=std::env::temp_dir().join(format!("km-ground-object-source-{}.ofn",std::process::id()));
    std::fs::write(&path,source).unwrap();
    let out=Command::new(env!("CARGO_BIN_EXE_km")).env("KM_GROUND_RULE_SOURCE","1")
        .args(["classify","--route","auto"]).arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
    let result:serde_json::Value=serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(result["consistent"],true); assert_eq!(result["dropped"],0);
    assert!(!result.to_string().contains("urn:km:ground-rule#"),"private classes leaked: {result}");
    assert!(result["subsumptions"].as_array().unwrap().contains(
        &serde_json::json!(["http://km.test/C","http://km.test/Bad"])),"{result}");
}
