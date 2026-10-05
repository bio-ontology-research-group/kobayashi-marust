use std::process::Command;

fn classify(fixture: &str) -> serde_json::Value {
    let input = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures").join(fixture);
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "ht_bridge"])
        .arg(input).output().expect("run km classification");
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    output
}

#[test]
fn cached_disjunctions_do_not_refute_acyl_subsumption() {
    let output = classify("cached_acyl_model.ofn");
    let pairs = output["subsumptions"].as_array().unwrap();
    assert!(pairs.contains(&serde_json::json!([
        "http://ontology.dumontierlab.com/AcylHalideGroup",
        "http://ontology.dumontierlab.com/AcylGroup",
    ])), "the symmetric bond and disjoint halogen force two distinct neighbors");
    assert!(!pairs.contains(&serde_json::json!([
        "http://ontology.dumontierlab.com/AcylGroup",
        "http://ontology.dumontierlab.com/AcylHalideGroup",
    ])));
}

#[test]
fn cached_successors_do_not_refute_slovenia_subsumption() {
    // The explicit production bridge route reliably reproduces the failure;
    // default portfolio runs can return an answer from a different worker.
    for _ in 0..12 {
        let output = classify("cached_slovenia_model.ofn");
        let pairs = output["subsumptions"].as_array().unwrap();
        assert!(pairs.contains(&serde_json::json!([
            "http://harmonisa.uni-klu.ac.at/ontology/corine-si.owl#AgriculturalAreas",
            "http://harmonisa.uni-klu.ac.at/ontology/corine-si.owl#SloveniaArea",
        ])), "AgriculturalSurface is a Surface and the other restrictions coincide");
        assert!(!pairs.contains(&serde_json::json!([
            "http://harmonisa.uni-klu.ac.at/ontology/corine-si.owl#SloveniaArea",
            "http://harmonisa.uni-klu.ac.at/ontology/corine-si.owl#AgriculturalAreas",
        ])));
    }
}

#[test]
fn saturated_successor_replay_preserves_inverse_universal_subsumption() {
    let output = classify("saturated_inverse_universal_model.ofn");
    let pairs = output["subsumptions"].as_array().unwrap();
    assert!(pairs.contains(&serde_json::json!([
        "http://ontology.neuinfo.org/NIF/BiomaterialEntities/NIF-GrossAnatomy.owl#nlx_anat_20090306",
        "http://ontology.neuinfo.org/NIF/BiomaterialEntities/NIF-GrossAnatomy.owl#birnlex_1496",
    ])), "the inverse edge must receive the universal forced by the disjoint transitive part");
    assert!(!pairs.contains(&serde_json::json!([
        "http://ontology.neuinfo.org/NIF/BiomaterialEntities/NIF-GrossAnatomy.owl#birnlex_1496",
        "http://ontology.neuinfo.org/NIF/BiomaterialEntities/NIF-GrossAnatomy.owl#nlx_anat_20090306",
    ])));
}
