//! The native bridge must count an at-most restriction's role through the
//! role hierarchy. A successor created for `∃r.C` carries one link per signed
//! super role of `r`; the successor scan used by ≤n/∀ previously inspected
//! only the FIRST link to each successor (the `r`-link), so `B ⊑ ≤1 q` with
//! `r ⊑ q` (or inverse functionality expressed through a named inverse role)
//! never merged the two `r`-successors and the bridge published an
//! incomplete taxonomy (ORE 13859: 17 missing `X ⊑ A ⊓ ∃r.C ⊓ ∀r.C`).
use std::process::Command;

fn bridge_subsumes_a_d(rbox_and_restriction: &str, role: &str) -> bool {
    let source = format!(
        "Ontology(<urn:t>\n\
         Declaration(Class(<urn:t#A>)) Declaration(Class(<urn:t#B>)) Declaration(Class(<urn:t#C>)) Declaration(Class(<urn:t#D>))\n\
         Declaration(ObjectProperty(<urn:t#r>)) Declaration(ObjectProperty(<urn:t#s>)) Declaration(ObjectProperty(<urn:t#q>))\n\
         SubClassOf(<urn:t#A> ObjectSomeValuesFrom({role} <urn:t#C>))\nSubClassOf(<urn:t#A> <urn:t#B>)\n{rbox_and_restriction}\n\
         EquivalentClasses(<urn:t#D> ObjectIntersectionOf(<urn:t#B> ObjectSomeValuesFrom({role} <urn:t#C>) ObjectAllValuesFrom({role} <urn:t#C>))))\n"
    );
    let dir = std::env::temp_dir().join(format!("km-bridge-atmost-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let path = dir.join(format!("case-{id}-{}.ofn", rbox_and_restriction.len()));
    std::fs::write(&path, &source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "ht_bridge"])
        .arg(&path)
        .output()
        .expect("run km classification");
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    output["subsumptions"]
        .as_array()
        .unwrap()
        .contains(&serde_json::json!(["urn:t#A", "urn:t#D"]))
}

#[test]
fn at_most_on_a_super_role_counts_sub_role_successors() {
    assert!(bridge_subsumes_a_d(
        "SubObjectPropertyOf(<urn:t#r> <urn:t#q>) SubClassOf(<urn:t#B> ObjectMaxCardinality(1 <urn:t#q>))",
        "<urn:t#r>"
    ));
}

#[test]
fn inverse_functionality_of_a_named_inverse_makes_the_role_functional() {
    assert!(bridge_subsumes_a_d(
        "InverseObjectProperties(<urn:t#s> <urn:t#r>) InverseFunctionalObjectProperty(<urn:t#s>)",
        "<urn:t#r>"
    ));
    assert!(bridge_subsumes_a_d("InverseFunctionalObjectProperty(<urn:t#s>)", "ObjectInverseOf(<urn:t#s>)"));
    assert!(bridge_subsumes_a_d(
        "SubClassOf(<urn:t#B> ObjectMaxCardinality(1 ObjectInverseOf(<urn:t#s>)))",
        "ObjectInverseOf(<urn:t#s>)"
    ));
}

#[test]
fn direct_at_most_still_entails_and_absent_restriction_does_not() {
    assert!(bridge_subsumes_a_d("SubClassOf(<urn:t#B> ObjectMaxCardinality(1 <urn:t#r>))", "<urn:t#r>"));
    assert!(!bridge_subsumes_a_d("SubObjectPropertyOf(<urn:t#r> <urn:t#q>)", "<urn:t#r>"));
}
