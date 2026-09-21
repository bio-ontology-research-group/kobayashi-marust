use std::process::Command;
#[test]
fn floating_data_preserves_owl_value_identity() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/floating-ground-data-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("float-aliases", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "16777217"^^xsd:float)
 DataPropertyAssertion(<http://e/p> <http://e/a> "16777216"^^xsd:float))"#, true),
        ("float-signed-zero", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "0"^^xsd:float)
 DataPropertyAssertion(<http://e/p> <http://e/a> "-0"^^xsd:float))"#, false),
        ("double-signed-zero", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "0"^^xsd:double)
 DataPropertyAssertion(<http://e/p> <http://e/a> "-0"^^xsd:double))"#, false),
        ("separate-primitive-spaces", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:float)
 DataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:double))"#, false),
        ("float-nan", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "NaN"^^xsd:float)
 DataPropertyAssertion(<http://e/p> <http://e/a> "NaN"^^xsd:float))"#, true),
        ("double-aliases", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "1.0"^^xsd:double)
 DataPropertyAssertion(<http://e/p> <http://e/a> "1E0"^^xsd:double))"#, true),
        ("positive-infinity", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "INF"^^xsd:float)
 DataPropertyAssertion(<http://e/p> <http://e/a> "+INF"^^xsd:float))"#, true),
        ("opposite-infinities", r#"Ontology(
 FunctionalDataProperty(<http://e/p>)
 DataPropertyAssertion(<http://e/p> <http://e/a> "INF"^^xsd:double)
 DataPropertyAssertion(<http://e/p> <http://e/a> "-INF"^^xsd:double))"#, false),
    ];
    for (name, source, expected) in cases {
        let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "nominals", "ht_general"] {
            for isolated in [false, true] {
                let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
                command.args(["classify", "--route", route]).arg(&path);
                if isolated { command.env("KM_NO_INPROC_HT", "1"); }
                else { command.env_remove("KM_NO_INPROC_HT"); }
                let out = command.output().unwrap();
                assert!(out.status.success(), "{name}/{route}/{isolated}: {}", String::from_utf8_lossy(&out.stderr));
                let result: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
                assert_eq!(result["consistent"], expected, "{name}/{route}/{isolated}");
                assert_eq!(result["dropped"], 0, "{name}/{route}/{isolated}");
                assert!(!String::from_utf8_lossy(&out.stdout).contains("__km_ground_data_"));
            }
        }
        std::fs::remove_file(path).unwrap();
    }
}
