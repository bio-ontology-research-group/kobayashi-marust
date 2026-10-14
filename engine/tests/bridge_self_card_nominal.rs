//! A SELF-bearing terminology (here global reflexivity) on the native
//! cardinality+ABox profile. Approximation saturation refuses SELF, and the
//! conditional-full schedule used to turn that refusal into a defer
//! (ORE 8294 / 10908). The exact nominal-only completion schedule must decide
//! these inputs instead, agreeing with the nominal CB calculus.
use std::process::Command;

const SOURCE: &str = "Ontology(<urn:s>
Declaration(Class(<urn:s#A>)) Declaration(Class(<urn:s#B>)) Declaration(Class(<urn:s#C>)) Declaration(Class(<urn:s#D>))
Declaration(ObjectProperty(<urn:s#r>)) Declaration(ObjectProperty(<urn:s#p>))
Declaration(NamedIndividual(<urn:s#a>)) Declaration(NamedIndividual(<urn:s#b>))
ReflexiveObjectProperty(<urn:s#r>)
FunctionalObjectProperty(<urn:s#p>)
SubClassOf(<urn:s#A> ObjectSomeValuesFrom(<urn:s#p> <urn:s#B>))
SubClassOf(<urn:s#A> ObjectAllValuesFrom(<urn:s#p> <urn:s#C>))
EquivalentClasses(<urn:s#D> ObjectSomeValuesFrom(<urn:s#p> ObjectIntersectionOf(<urn:s#B> <urn:s#C>)))
SubClassOf(<urn:s#B> ObjectSomeValuesFrom(<urn:s#r> <urn:s#B>))
ClassAssertion(<urn:s#A> <urn:s#a>)
ObjectPropertyAssertion(<urn:s#p> <urn:s#a> <urn:s#b>)
EXTRA
)";

fn classify(route: &str, extra: &str, name: &str) -> serde_json::Value {
    let dir = std::env::temp_dir().join(format!("km-bridge-self-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}-{route}.ofn"));
    std::fs::write(&path, SOURCE.replace("EXTRA", extra)).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let result = command
        .args(["classify", "--route", route])
        .arg(&path)
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_THREADS", "1")
        .output()
        .expect("run km classification");
    assert!(
        result.status.success(),
        "{route}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&result.stdout).unwrap()
}

#[test]
fn self_terminology_card_nominal_bridge_decides_by_completion() {
    let consistent_extra = "DifferentIndividuals(<urn:s#a> <urn:s#b>)";
    let bridge = classify("ht_bridge", consistent_extra, "consistent");
    let exact = classify("nominals", consistent_extra, "consistent");
    assert_eq!(bridge["consistent"], true);
    assert_eq!(bridge["dropped"], 0);
    assert_eq!(bridge["subsumptions"], exact["subsumptions"]);
    assert!(bridge["subsumptions"]
        .as_array()
        .unwrap()
        .contains(&serde_json::json!(["urn:s#A", "urn:s#D"])));

    let clash_extra = "Declaration(NamedIndividual(<urn:s#c>)) \
        ObjectPropertyAssertion(<urn:s#p> <urn:s#a> <urn:s#c>) \
        DifferentIndividuals(<urn:s#a> <urn:s#b> <urn:s#c>)";
    let bridge = classify("ht_bridge", clash_extra, "clash");
    let exact = classify("nominals", clash_extra, "clash");
    assert_eq!(bridge["consistent"], false);
    assert_eq!(exact["consistent"], false);
}
