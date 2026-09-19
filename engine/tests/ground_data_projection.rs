use std::process::Command;

#[test]
fn ground_data_preserves_domains_without_putting_literals_in_object_domain() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/ground-data-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("singleton", r#"Ontology(
          EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))
          DataPropertyAssertion(<http://e/p> <http://e/a> "zero")
          DataPropertyAssertion(<http://e/p> <http://e/a> "one"))"#, true),
        ("union-clash", r#"Ontology(
          DataPropertyDomain(<http://e/q> ObjectUnionOf(<http://e/A> <http://e/B>))
          SubDataPropertyOf(<http://e/p> <http://e/q>)
          DataPropertyRange(<http://e/q> DataOneOf("ok" "other"))
          DataPropertyAssertion(<http://e/p> <http://e/a> "ok")
          ClassAssertion(ObjectComplementOf(<http://e/A>) <http://e/a>)
          ClassAssertion(ObjectComplementOf(<http://e/B>) <http://e/a>))"#, false),
        ("union-consistent", r#"Ontology(
          DataPropertyDomain(<http://e/p> ObjectUnionOf(<http://e/A> <http://e/B>))
          DataPropertyAssertion(<http://e/p> <http://e/a> "ok")
          ClassAssertion(ObjectComplementOf(<http://e/A>) <http://e/a>))"#, true),
        ("same-owner", r#"Ontology(
          DataPropertyAssertion(<http://e/p> <http://e/a> "one")
          DataPropertyAssertion(<http://e/p> <http://e/b> "two")
          SameIndividual(<http://e/a> <http://e/b>))"#, true),
        ("duplicate-domains", r#"Ontology(
          DataPropertyDomain(<http://e/p> <http://e/C>)
          ClassAssertion(<http://e/C> <http://e/a>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "one")
          DataPropertyAssertion(<http://e/p> <http://e/a> "two"))"#, true),
        ("nominal-domain", r#"Ontology(
          Declaration(Class(<http://e/N>)) Declaration(Class(<http://e/C>))
          EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>))
          DataPropertyDomain(<http://e/p> <http://e/C>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "value"))"#, true),
    ];
    for (name, source, expected) in cases {
        let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "nominals"] {
            let out = Command::new(env!("CARGO_BIN_EXE_km"))
                .args(["classify", "--route", route]).arg(&path).output().unwrap();
            assert!(out.status.success(), "{name}/{route}: {}", String::from_utf8_lossy(&out.stderr));
            let result: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
            assert_eq!(result["consistent"], expected, "{name}/{route}");
            assert_eq!(result["dropped"], 0, "{name}/{route}");
            if name == "nominal-domain" {
                assert!(result["subsumptions"].as_array().unwrap()
                    .contains(&serde_json::json!(["http://e/N", "http://e/C"])), "{route}: {result}");
            }
        }
        std::fs::remove_file(path).unwrap();
    }
}
