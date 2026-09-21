use std::process::Command;
#[test]
fn ground_ranges_preserve_membership_and_reject_proved_violations() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/ground-range-clash-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("empty-string", r#"Ontology(DataPropertyRange(<http://e/p> DataOneOf("all" "driver" "driver and front passenger")) DataPropertyAssertion(<http://e/p> <http://e/a> ""))"#, false),
        ("admitted-string", r#"Ontology(DataPropertyRange(<http://e/p> DataOneOf("all" "driver")) DataPropertyAssertion(<http://e/p> <http://e/a> "driver"^^xsd:string))"#, true),
        ("integer-bound", r#"Ontology(DataPropertyRange(<http://e/p> xsd:positiveInteger) DataPropertyAssertion(<http://e/p> <http://e/a> "0"^^xsd:int))"#, false),
        ("inherited-range", r#"Ontology(SubDataPropertyOf(<http://e/q> <http://e/p>) DataPropertyRange(<http://e/p> xsd:string) DataPropertyAssertion(<http://e/q> <http://e/a> "1"^^xsd:int))"#, false),
        ("float-enumeration", r#"Ontology(DataPropertyRange(<http://e/p> DataOneOf("0"^^xsd:float)) DataPropertyAssertion(<http://e/p> <http://e/a> "-0"^^xsd:float))"#, false),
        ("integer-enumeration", r#"Ontology(DataPropertyRange(<http://e/p> DataOneOf("+01"^^xsd:int)) DataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:integer))"#, true),
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
