use std::process::Command;
#[test]
fn finite_membership_preserves_data_and_object_interactions() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/finite-data-membership-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let cases = [
        ("anonymous-alias-clash", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "+01"^^xsd:int) _:genid95) NegativeDataPropertyAssertion(<http://e/p> _:genid95 "1"^^xsd:integer))"#, false),
        ("anonymous-owner-control", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95) NegativeDataPropertyAssertion(<http://e/p> _:genid96 "v"))"#, true),
        ("anonymous-same-owner", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95) NegativeDataPropertyAssertion(<http://e/p> <http://e/a> "v") SameIndividual(_:genid95 <http://e/a>))"#, false),
        ("anonymous-collision-control", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95) NegativeDataPropertyAssertion(<http://e/p> <http://e/genid95> "v"))"#, true),
        ("anonymous-role-link", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95) ClassAssertion(ObjectAllValuesFrom(<http://e/r> ObjectComplementOf(DataHasValue(<http://e/p> "v"))) <http://e/a>) ObjectPropertyAssertion(<http://e/r> <http://e/a> _:genid95))"#, false),
        ("anonymous-oneof-control", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") _:genid95) ClassAssertion(ObjectOneOf(_:genid95) <http://e/a>))"#, true),
        ("top-data-control", r#"Ontology(SubClassOf(<http://e/A> DataHasValue(<http://e/p> "v")) SubDataPropertyOf(<http://e/p> owl:topDataProperty) ClassAssertion(<http://e/A> <http://e/a>))"#, true),
        ("top-data-clash", r#"Ontology(SubClassOf(<http://e/A> DataHasValue(<http://e/p> "v")) SubDataPropertyOf(<http://e/p> <http://www.w3.org/2002/07/owl#topDataProperty>) ClassAssertion(<http://e/A> <http://e/a>) NegativeDataPropertyAssertion(<http://e/p> <http://e/a> "v"))"#, false),
        ("alias-clash", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "+01"^^xsd:int) <http://e/a>) NegativeDataPropertyAssertion(<http://e/p> <http://e/a> "1"^^xsd:integer))"#, false),
        ("negative-control", r#"Ontology(ClassAssertion(ObjectComplementOf(DataHasValue(<http://e/p> "v")) <http://e/a>) DataPropertyAssertion(<http://e/p> <http://e/a> "other"))"#, true),
        ("inherited-functional-clash", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyAssertion(<http://e/q> <http://e/a> "other") SubDataPropertyOf(<http://e/p> <http://e/q>) FunctionalDataProperty(<http://e/q>))"#, false),
        ("distinct-owners", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyAssertion(<http://e/p> <http://e/b> "other") FunctionalDataProperty(<http://e/p>))"#, true),
        ("same-individual", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyAssertion(<http://e/p> <http://e/b> "other") FunctionalDataProperty(<http://e/p>) SameIndividual(<http://e/a> <http://e/b>))"#, false),
        ("range-clash", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyRange(<http://e/p> DataOneOf("other")))"#, false),
        ("domain-clash", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyDomain(<http://e/p> <http://e/A>) ClassAssertion(ObjectComplementOf(<http://e/A>) <http://e/a>))"#, false),
        ("equivalent-negative", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) EquivalentDataProperties(<http://e/p> <http://e/q>) NegativeDataPropertyAssertion(<http://e/q> <http://e/a> "v"))"#, false),
        ("disjoint-properties", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) DataPropertyAssertion(<http://e/q> <http://e/a> "v") DisjointDataProperties(<http://e/p> <http://e/q>))"#, false),
        ("object-existential", r#"Ontology(ClassAssertion(ObjectSomeValuesFrom(<http://e/r> DataHasValue(<http://e/p> "v")) <http://e/a>) SubClassOf(DataHasValue(<http://e/p> "v") owl:Nothing))"#, false),
        ("private-name", r#"Ontology(ClassAssertion(DataHasValue(<http://e/p> "v") <http://e/a>) ClassAssertion(ObjectComplementOf(<http://e/__km_data_member_p0_v0>) <http://e/a>))"#, true),
    ];
    for (name, source, expected) in cases {
        let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "nominals", "ht_bridge"] {
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
                assert!(!String::from_utf8_lossy(&out.stdout).contains("__km_data_member_"));
            }
        }
        std::fs::remove_file(path).unwrap();
    }
}
