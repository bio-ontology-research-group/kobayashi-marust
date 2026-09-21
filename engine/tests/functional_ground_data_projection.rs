use std::process::Command;

#[test]
fn functional_data_preserves_value_identity_and_owner_equality() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/functional-ground-data-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("canonical-integers", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          DataPropertyRange(<http://e/p> xsd:integer)
          DataPropertyAssertion(<http://e/p> <http://e/a> "+001"^^xsd:int)
          DataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:integer))"#, true),
        ("inverse-functional-clash", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          InverseFunctionalObjectProperty(<http://e/link>)
          ObjectPropertyAssertion(<http://e/link> <http://e/a> <http://e/c>)
          ObjectPropertyAssertion(<http://e/link> <http://e/b> <http://e/c>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "left")
          DataPropertyAssertion(<http://e/p> <http://e/b> "right"))"#, false),
        ("distinct-owners", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "left")
          DataPropertyAssertion(<http://e/p> <http://e/b> "right"))"#, true),
        ("singleton-functional-clash", r#"Ontology(
          EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "left")
          DataPropertyAssertion(<http://e/p> <http://e/b> "right"))"#, false),
        ("inherited-functional-clash", r#"Ontology(
          EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))
          SubDataPropertyOf(<http://e/q> <http://e/p>)
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/q> <http://e/a> "1"^^xsd:int)
          DataPropertyAssertion(<http://e/p> <http://e/b> "2"^^xsd:int))"#, false),
        ("independent-properties", r#"Ontology(
          FunctionalDataProperty(<http://e/p>) FunctionalDataProperty(<http://e/q>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "left")
          DataPropertyAssertion(<http://e/p> <http://e/b> "right")
          DataPropertyAssertion(<http://e/q> <http://e/a> "right")
          DataPropertyAssertion(<http://e/q> <http://e/b> "left"))"#, true),
        ("canonical-booleans", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "true"^^xsd:boolean)
          DataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:boolean))"#, true),
        ("unused-object", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          ClassAssertion(<http://e/C> <http://e/unused>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "left")
          DataPropertyAssertion(<http://e/p> <http://e/b> "right"))"#, true),
        ("singleton-equal-values", r#"Ontology(
          EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "true"^^xsd:boolean)
          DataPropertyAssertion(<http://e/p> <http://e/b> "1"^^xsd:boolean))"#, true),
        ("escaped-strings", r#"Ontology(
          FunctionalDataProperty(<http://e/p>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "a\"b\\c")
          DataPropertyAssertion(<http://e/p> <http://e/a> "a\"b\\c"^^xsd:string))"#, true),
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
            assert!(!String::from_utf8_lossy(&out.stdout).contains("__km_ground_data_"));
        }
        std::fs::remove_file(path).unwrap();
    }
}
