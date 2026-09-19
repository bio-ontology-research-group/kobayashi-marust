use kobayashi_marust::frontend::{iri::IriRegistry, normalise, parse, rbox};
use std::process::Command;

#[test]
fn inverse_chain_keeps_both_typed_converse_definitions() {
    let text = "Ontology(SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(<r>) <s>) ObjectInverseOf(<t>)))";
    let mut reg = IriRegistry::new();
    let ontology = parse::parse_axioms(&mut reg, text).unwrap();
    let (_, _, hooks) = normalise::normalise(&ontology);
    let mut rows = Vec::new();
    parse::for_each_ontology_child(text, |node| {
        rbox::rbox_node(&mut reg, node, &mut rows);
        Ok(())
    }).unwrap();
    for (base, proxy) in [("r", "__inv__r"), ("t", "__inv__t")] {
        assert!(hooks.role_inverses.contains(&(base.into(), proxy.into())));
        assert!(rows.contains(&rbox::RboxRecord::Inverse(base.into(), proxy.into())));
    }
    assert!(rows.contains(&rbox::RboxRecord::Chain("__inv__r".into(), "s".into(), "__inv__t".into())));
    assert!(!rows.iter().any(|r| matches!(r, rbox::RboxRecord::Fenced(..))));
}

#[test]
fn inverse_chain_rejects_malformed_inverse_expressions() {
    for expr in ["ObjectInverseOf()", "ObjectInverseOf(<r> <s>)", "ObjectInverseOf(ObjectInverseOf(<r>))"] {
        let text = format!("Ontology(SubObjectPropertyOf(ObjectPropertyChain({expr} <s>) <t>))");
        assert!(parse::parse_axioms(&mut IriRegistry::new(), &text).is_err());
    }
}

#[test]
fn inverse_chain_classification_checks_direction_and_source_name_collision() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/inverse-chain-tests");
    std::fs::create_dir_all(&dir).unwrap();
    for (name, forbidden, expected) in [("entailed", "<t> <c> <a>", false),
        ("reversed", "<t> <a> <c>", true),
        ("source_collision", "<__inv__r> <a> <b>", true)] {
        // r(b,a), s(b,c), inv(r) o s <= inv(t) entails t(c,a).
        // It entails neither the reversed t edge nor an unrelated source role
        // whose legal local name happens to look like an internal inverse.
        let text = format!("Ontology(
          Declaration(ObjectProperty(<__inv__r>))
          SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(<r>) <s>) ObjectInverseOf(<t>))
          ObjectPropertyAssertion(<r> <b> <a>)
          ObjectPropertyAssertion(<s> <b> <c>)
          NegativeObjectPropertyAssertion({forbidden}))");
        let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
        std::fs::write(&path, text).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
        std::fs::remove_file(path).unwrap();
        assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
        let answer: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(answer["consistent"], expected, "{name}");
        assert_eq!(answer["dropped"], 0, "{name}: no constraint may be discarded");
    }
}
