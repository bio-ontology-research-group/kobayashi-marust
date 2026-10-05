use std::process::Command;

#[test]
fn redundant_rule_reduction_retains_transitivity_for_negative_abox_checks() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let input = std::env::temp_dir().join(format!("km-trans-rule-{}-{unique}.ofn", std::process::id()));
    let source = r#"Ontology(
        Declaration(Class(<http://km.test/C>))
        Declaration(ObjectProperty(<http://km.test/r>))
        ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
        ObjectPropertyAssertion(<http://km.test/r> <http://km.test/b> <http://km.test/c>)
        NegativeObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/c>)
        TransitiveObjectProperty(<http://km.test/r>)
        DLSafeRule(Body(
            ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/y>))
            ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/y>) Variable(<http://km.test/z>))
            DifferentIndividualsAtom(Variable(<http://km.test/x>) Variable(<http://km.test/z>)))
            Head(ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/z>))))
    )"#;
    let inverse_chain = source
        .replacen("Ontology(", "Ontology(Declaration(ObjectProperty(<http://km.test/s>)) Declaration(ObjectProperty(<http://km.test/t>))", 1)
        .replace("ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)",
            "ObjectPropertyAssertion(<http://km.test/r> <http://km.test/b> <http://km.test/a>)")
        .replace("ObjectPropertyAssertion(<http://km.test/r> <http://km.test/b> <http://km.test/c>)",
            "ObjectPropertyAssertion(<http://km.test/s> <http://km.test/b> <http://km.test/c>)")
        .replace("NegativeObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/c>)",
            "NegativeObjectPropertyAssertion(<http://km.test/t> <http://km.test/a> <http://km.test/c>)\nSubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(<http://km.test/r>) <http://km.test/s>) <http://km.test/t>)");
    let unrelated = source.replace(
        "NegativeObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/c>)",
        "NegativeObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/d>)",
    );
    for (variant, ontology, consistent) in [
        ("transitive", source, false),
        ("inverse-chain", inverse_chain.as_str(), false),
        ("unrelated-negative", unrelated.as_str(), true),
    ] {
      std::fs::write(&input, ontology).unwrap();
      for reduction in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env("KM_NOMINALS", "1").env_remove("KM_RULE_ASSERTION_CLOSURE")
            .env_remove("KM_TRANSITIVE_RULE_REDUCE");
        if reduction { command.env("KM_TRANSITIVE_RULE_REDUCE", "1"); }
        let result = command.args(["classify", "--route", "auto"]).arg(&input).output().unwrap();
        assert!(result.status.success(), "{variant}, reduction={reduction}: {}", String::from_utf8_lossy(&result.stderr));
        let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(output["consistent"], consistent, "RBox consequence must survive {variant}, reduction={reduction}: {output}");
      }
    }
    std::fs::remove_file(input).unwrap();
}
